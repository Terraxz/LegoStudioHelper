"""
🧰 LEGO Studio Helper
---------------------------

This Python utility helps safeguard your LEGO Studio instructions from unexpected corruption.
It offers automatic backups and a repair tool to restore lost/corrupted instruction data.

Features:
- Select a `.io` file to begin.
- Press "Create Backup" to manually save a copy.
- Enable "Autobackup" to monitor changes and auto-save every few minutes.
- Backups are stored in the `IObackups` folder next to your original file.

Repair Workflow:
- LEGO Studio may corrupt instructions after major build changes.
- Use this app to recover instructions from a valid backup.
- Select the most recent backup with correct instructions.
- Select your latest (corrupted) file.
- Press "Fix" to generate a new file with restored instructions.
- The original file is never overwritten.

License:
This code is released under the MIT License.
You are free to use, modify, and distribute it as you wish.

Support:
If you enjoy this app, please follow me on rebrickable:
https://rebrickable.com/users/Terraxz/mocs/


"""



from ast import Index
from hmac import new
from itertools import count
import tkinter as tk
from tkinter import filedialog
import configparser
import os
import shutil
from datetime import datetime
from pathlib import Path
import zipfile
import json
import xml.etree.ElementTree as ET
from collections import defaultdict
from collections import Counter
import webbrowser
import threading
import time
from pathlib import Path
from datetime import datetime

# ─────────────────────────────────────────────
# 🧩 Subroutines
# ─────────────────────────────────────────────


def save_config(key, value, filename="settings.json"):
    if os.path.exists(filename):
        with open(filename, "r") as f:
            try:
                config = json.load(f)
            except json.JSONDecodeError:
                config = {}
    else:
        config = {}

    config[key] = value

    with open(filename, "w") as f:
        json.dump(config, f, indent=4)


def load_config(key, default=None, filename="settings.json"):
    if os.path.exists(filename):
        with open(filename, "r") as f:
            try:
                config = json.load(f)
                return config.get(key, default)
            except json.JSONDecodeError:
                return default
    return default





def add_brick_data(stepdata, xml_data):
    import xml.etree.ElementTree as ET

    tree = ET.ElementTree(ET.fromstring(xml_data))
    root = tree.getroot()

    # Build uuid → itemNos lookup from <Bricks>
    uuid_to_itemNos = {
        brick.get("uuid"): brick.get("itemNos")
        for brick in root.find("Bricks").findall("Brick")
        if brick.get("uuid") and brick.get("itemNos")
    }

    # Recursive enrichment
    def enrich_step(step):
        uuids = step.get("uuids", [])
        itemNos = [uuid_to_itemNos.get(uuid) for uuid in uuids if uuid_to_itemNos.get(uuid)]
        if itemNos:
            step["itemNos"] = itemNos

        # Recurse into children
        if "children" in step:
            for group in step["children"]:
                for child in group:
                    enrich_step(child)

    for top_step in stepdata:
        enrich_step(top_step)

    return stepdata




def remove_deleted_steps_and_flatten(nested_steps):
    flat_steps = []

    def flatten(step):
        # Skip deleted steps
        if step.get("delete"):
            return

        # Process children first
        if "children" in step:
            for group in step["children"]:
                for child in group:
                    flatten(child)

        # Then add the current step
        flat_steps.append({k: v for k, v in step.items() if k != "children"})

    for top_step in nested_steps:
        flatten(top_step)

    return flat_steps



def mark_for_deletion(raw_steps):
    def mark(step):
        if step.get("buildtotal", 0) > 1:
            step["delete"] = True

        # Recurse into children
        if "children" in step:
            for group in step["children"]:
                for child in group:
                    mark(child)

    for top_step in raw_steps:
        mark(top_step)

    return raw_steps


def cleanup_and_paginate_steps(flat_steps):
    cleaned = []
    page_counter = 1

    for step in flat_steps:
        # Remove unwanted keys
        stripped = {k: v for k, v in step.items() if k not in ["Build", "buildtotal", "subbuild_refID"]}

        # Separate 'children' if present
        children = stripped.pop("children", None)

        # Add 'page' at the top
        reordered = {"PageStep": page_counter}
        reordered.update(stripped)

        # Append 'children' at the end
        if children is not None:
            reordered["children"] = children

        cleaned.append(reordered)
        page_counter += 1

    return cleaned




def enrich_steps_with_names3(raw_steps, xml_data):
    import xml.etree.ElementTree as ET
    from collections import defaultdict

    tree = ET.ElementTree(ET.fromstring(xml_data))
    root = tree.getroot()

    config_section = root.find("Configurations")
    extracted = []

    # First pass: collect names
    def collect_names(build_elem, skip_first, name_counts):
        name = build_elem.get("name")
        if name:
            if skip_first[0]:
                skip_first[0] = False
            else:
                name_counts[name] += 1
                extracted.append((name, name_counts[name]))
        child_counts = defaultdict(int)
        for child in build_elem.findall("Build"):
            collect_names(child, [False], child_counts)

    if config_section is not None:
        config_wrapper = config_section.find("Configuration")
        if config_wrapper is not None:
            top_builds = config_wrapper.findall("Build")
            if top_builds:
                collect_names(top_builds[0], [True], defaultdict(int))

    refid_to_name = {str(i): name for i, (name, _) in enumerate(extracted)}

    # Track Build numbers per (subbuild_refID, ParentGroup)
    build_assignments = {}
    build_counters = defaultdict(int)

    def enrich_step(step):
        refid = step.get("subbuild_refID")
        parent = step.get("ParentGroup")
        if refid is not None:
            name = refid_to_name.get(str(refid))
            if name:
                step["subbuild_name"] = name
                key = (refid, parent)
                if key not in build_assignments:
                    build_counters[(name, parent)] += 1
                    build_assignments[key] = build_counters[(name, parent)]
                step["Build"] = build_assignments[key]

        if "children" in step:
            for child_group in step["children"]:
                for child in child_group:
                    enrich_step(child)

    for top_step in raw_steps:
        enrich_step(top_step)

    return raw_steps



def reassign_build_numbers_by_parentgroup(enriched_steps):
    from collections import defaultdict

    # Track counts per (name, ParentGroup)
    build_counters = defaultdict(lambda: defaultdict(int))

    def process_step(step):
        name = step.get("subbuild_name")
        parent = step.get("ParentGroup")

        if name is not None:
            count = build_counters[name][parent] + 1
            build_counters[name][parent] = count
            step["Build"] = count

        # Recurse into children
        for child_group in step.get("children", []):
            for child in child_group:
                process_step(child)

    for top_step in enriched_steps:
        process_step(top_step)

    return enriched_steps




def add_group_data(step_json, xml_data):
    """
    Adds 'GroupRefId' and 'ParentGroup' to each step in the JSON.
    GroupRefId is assigned sequentially from XML <Group refID>, skipping refID="1".
    ParentGroup is inherited from the parent step's GroupRefId.
    """

    def extract_group_ids(xml_data):
        root = ET.fromstring(xml_data)
        group_ids = []
        for group in root.findall(".//Group"):
            ref_id = int(group.attrib.get("refID", "0"))
            if ref_id > 1:
                group_ids.append(ref_id)
        return group_ids

    def assign_group_ids(steps, group_ids, counter, parent_group=None):
        for step in steps:
            # Assign current GroupRefId
            if counter[0] < len(group_ids):
                step["GroupRefId"] = group_ids[counter[0]]
                counter[0] += 1
            else:
                step["GroupRefId"] = None  # fallback

            # Assign ParentGroup
            step["ParentGroup"] = parent_group

            # Recurse into children
            if "children" in step and step["children"]:
                for child_group in step["children"]:
                    assign_group_ids(child_group, group_ids, counter, parent_group=step["GroupRefId"])

    group_ids = extract_group_ids(xml_data)
    assign_group_ids(step_json, group_ids, counter=[0])
    return step_json




def extract_nested_steps(xml_data):
    import xml.etree.ElementTree as ET

    tree = ET.ElementTree(ET.fromstring(xml_data))
    root = tree.getroot()

    # Build refID → uuid lookup from <Bricks>
    brick_lookup = {
        brick.get("refID"): brick.get("uuid")
        for brick in root.find("Bricks").findall("Brick")
        if brick.get("refID") and brick.get("uuid")
    }

    def collect_nested(element, current_refid=None):
        steps = []

        for step in element.findall("Step"):
            step_id = step.get("refID")

            # Collect uuids from <In>
            uuids = [
                brick_lookup.get(in_elem.get("brickRef"))
                for in_elem in step.findall("In")
                if brick_lookup.get(in_elem.get("brickRef"))
            ]

            entry = {
                "step": step_id,
                "uuids": uuids,
                "children": []
            }

            if current_refid is not None:
                entry["subbuild_refID"] = current_refid

            # Recurse into nested SubBuilds
            for subbuild in step.findall("SubBuild"):
                subbuild_ref = subbuild.get("refID")
                entry["children"].append(collect_nested(subbuild, subbuild_ref))

            steps.append(entry)

        return steps

    steps_root = root.find("BuildingInstruction").find("Steps")
    if steps_root is None:
        print("No <Steps> section found.")
        return []

    return collect_nested(steps_root)




def add_build_totals(steps):
    def apply_build_total(step, parent_builds):
        # Get current build value, default to 0
        current_build = step.get("Build", 0)

        # Compute total: multiply all parent builds with current
        total_chain = parent_builds + [current_build]
        buildtotal = 1
        for b in total_chain:
            buildtotal *= b if b else 1  # treat 0 as neutral (1)

        step["buildtotal"] = buildtotal

        # Recurse into children
        if "children" in step:
            for group in step["children"]:
                for child in group:
                    apply_build_total(child, total_chain)

    for top_step in steps:
        apply_build_total(top_step, [])

    return steps



def add_template_data(step_json, xml_data):
    # Parse the XML string
    root = ET.fromstring(xml_data)

    # Collect templates and resizeBars in order of steps
    page_data = []
    for page in root.findall(".//Page"):
        template = page.attrib.get("template")
        resize_bars = page.attrib.get("resizeBars")
        steps = page.findall(".//Step")

        # Track TemplateStep per page
        for i, _ in enumerate(steps):
            page_data.append({
                "template": template,
                "resizeBars": resize_bars,
                "TemplateStep": i + 1  # 1-based index within the page
            })

    # Apply template, resizeBars, and TemplateStep to step_json
    for i, step in enumerate(step_json):
        if i < len(page_data):
            step["Template"] = page_data[i]["template"]
            step["TemplateStep"] = page_data[i]["TemplateStep"]
            if page_data[i]["resizeBars"] is not None:
                step["resizeBars"] = page_data[i]["resizeBars"]

    return step_json


def add_empty_pages(step_json, xml_data):
    root = ET.fromstring(xml_data)
    updated_json = []
    step_index = 0  # Tracks position in step_json

    for page in root.findall(".//Page"):
        template = page.attrib.get("template", "Unknown")
        slots = page.findall(".//Slot")

        for slot in slots:
            step = slot.find("Step")
            if step is not None:
                # Add the next step from the original JSON
                if step_index < len(step_json):
                    updated_json.append(step_json[step_index])
                    step_index += 1
            else:
                # Insert an empty page marker
                updated_json.append({
                    "PageStep": -1,
                    "EmptyPage": True,
                    "Template": template
                })

    # Append any remaining steps (if XML had fewer <Step> than JSON entries)
    while step_index < len(step_json):
        updated_json.append(step_json[step_index])
        step_index += 1

    return updated_json


def add_slot_data_to_steps(step_json, xml_data):
    root = ET.fromstring(xml_data)
    slot_elements = []

    # Collect all <Slot> elements, regardless of whether they contain a <Step>
    for page in root.findall(".//Page"):
        for slot in page.findall("Slot"):
            slot_xml = ET.tostring(slot, encoding="unicode")
            slot_elements.append(slot_xml)

    # Inject slot XML into step_json
    for i, step in enumerate(step_json):
        if i < len(slot_elements):
            step["XMLPageData"] = slot_elements[i]

    # Warning if mismatch
    if len(slot_elements) != len(step_json):
        print(f"⚠️ Warning: {len(slot_elements)} <Slot> elements found, but {len(step_json)} JSON steps provided.")

    return step_json

def add_counter(step_list):
    for i, step in enumerate(step_list, start=1):
        step["counter"] = i
    return step_list



def select_studio_file():
    path = filedialog.askopenfilename(title="Select Studio File", filetypes=[("Studio Files", "*.io")])
    if path:
        studio_path.set(path)
     

def create_backup():
    original = Path(studio_path.get())
    if not original.is_file():
        backup_path.set("No valid Studio file selected.")
        return

    backup_dir = original.parent / "IObackups"
    backup_dir.mkdir(exist_ok=True)

    timestamp = datetime.now().strftime("%Y-%m-%dT%H%M")
    backup_name = f"{original.stem}_backup_{timestamp}.io"
    backup_file = backup_dir / backup_name

    shutil.copy2(original, backup_file)
    backup_path.set(f"Backup saved: {backup_file.stem}")
 
      

def unpack_and_parse_io(io_path):
    if not zipfile.is_zipfile(io_path):
        print("Not a valid .io zip file.")
        return {"status": "error", "message": "Not a valid .io zip file."}

 
    with zipfile.ZipFile(io_path, 'r') as zip_ref:
        # List contents for debugging
        contents = zip_ref.namelist()
        #print("Contents:", contents)
           

        # Parse model.lxfml (XML)
        if "model.lxfml" in contents:
            with zip_ref.open("model.lxfml") as lxfml_file:
                try:
                    xml_data = lxfml_file.read().decode("utf-8")
                 
                    step_uuid_map = extract_nested_steps(xml_data)
                    step_uuid_map = add_brick_data(step_uuid_map,xml_data)
                    step_uuid_map = add_group_data(step_uuid_map,xml_data)
                    step_uuid_map = enrich_steps_with_names3(step_uuid_map, xml_data)
                    step_uuid_map = add_build_totals(step_uuid_map)

                    step_uuid_map = mark_for_deletion(step_uuid_map)
                    flatstep_uuid_map = remove_deleted_steps_and_flatten(step_uuid_map)
                    flatstep_uuid_map = cleanup_and_paginate_steps(flatstep_uuid_map )
                                    
                    #print("JSON PART 1")
                    #print(json.dumps(step_uuid_map, indent=2))

                    #print("JSON PART 2")
                    #print(json.dumps(flatstep_uuid_map, indent=2))
                          
                except Exception as e:
                    print("Error reading or parsing model.lxfml:", e)
                    return {"status": "error", "message": "Error reading or parsing model.lxfml."}

        else:
            print("model.lxfml not found in archive.")
            return {"status": "error", "message": "model.lxfml not found in archive."}

        # Extract and parse model.ins
        if "model.ins" in contents:
            with zip_ref.open("model.ins") as ins_file:
                try:
                   xml_data = ins_file.read().decode("utf-8")

                   
                   flatstep_uuid_map = add_template_data(flatstep_uuid_map, xml_data)
                   flatstep_uuid_map = add_empty_pages(flatstep_uuid_map, xml_data)
                   flatstep_uuid_map = add_slot_data_to_steps(flatstep_uuid_map, xml_data)
                   flatstep_uuid_map = add_counter(flatstep_uuid_map)

                   print(json.dumps(flatstep_uuid_map, indent=2))
                   print ("done\n\n\n")
                
                except ET.ParseError as e:
                    print("Error parsing model.ins:", e)
                    return {"status": "error", "message": "Error parsing model.ins"}

        else:
            print("model.ins not found in archive.")
            return {"status": "error", "message": "model.ins not found in archive."}
            
    return {
        "status": "ok",
        "data": flatstep_uuid_map
            }



import uuid
import xml.etree.ElementTree as ET

def create_default_step(index):
    slot_guid = str(uuid.uuid4())
    step_guid = str(uuid.uuid4())

    slot = ET.Element("Slot", {
        "GUID": slot_guid
    })

    step = ET.SubElement(slot, "Step", {
        "GUID": step_guid,
        "SerializedIndex": str(index),
        "RectOffset": "0 0 0 0"
    })

    ET.SubElement(step, "StepPreview", {
        "Depth": "-100",
        "targetPosOffset": "-16.22852 -40.08545 -16.50024",
        "IsForcedTargetPosOffset": "True",
        "DefaultCameraControlInfo_cameraScale": "170",
        "DefaultCameraControlInfo_TargetPos": "-34 -10 -25.00001",
        "DefaultCameraControlInfo_cameraAngle": "-0.5235988 0.7853982",
        "DefaultCameraControlInfo_modelAngle": "0 0 0"
    })

    ET.SubElement(step, "StepNumber", {
        "Depth": "-30"
    })

    ET.SubElement(step, "PartList", {
        "Rect": "0 0 0 0",
        "Depth": "-70"
    })

    submodel_preview = ET.SubElement(step, "SubmodelPreview", {
        "Depth": "-80",
        "Position": "0 0"
    })

    ET.SubElement(submodel_preview, "Multiplier", {
        "Position": "0 0"
    })

    return slot  # Return only the <Slot> element





def FindStep(goodjson, pagestep, uuids, itemnos):

    # Normalize input for comparison
    uuids_set = set(uuids)
    itemnos_set = set(itemnos)

    # First pass: match exact uuids
    for entry in goodjson:
        entry_uuids = set(entry.get("uuids", []))
        if entry_uuids == uuids_set:
            return entry.get("counter", -1)

    # Second pass: match exact itemNos
    matching_itemnos = []
    for entry in goodjson:
        entry_itemnos = set(entry.get("itemNos", []))
        if entry_itemnos == itemnos_set:
            matching_itemnos.append(entry)

    if len(matching_itemnos) == 1:
        return matching_itemnos[0].get("counter", -1)
    elif len(matching_itemnos) > 1:
        # Find closest PageStep
        closest = min(matching_itemnos, key=lambda x: abs(x.get("PageStep", 0) - pagestep))
        return closest.get("counter", -1)

    # No match found
    return -1


def correct_templates(data):
    corrected = []
    i = 0

    # Template grouping rules
    group_sizes = {
        "OneByTwo": 2,
        "TwoByOne": 2,
        "OneByThree": 3,
        "ThreeByOne": 3,
        "TwoByTwo_Col": 4,
        "TwoByTwo": 4,
        "ThreeByTwo": 6,
        "TwoByThree": 6
    }

    while i < len(data):
        entry = data[i]
        template = entry.get("Template")

        if template == "OneByOne":
            corrected.append(entry)
            i += 1
            continue

        group_size = group_sizes.get(template)
        if group_size:
            # Check if full group matches
            if i + group_size - 1 < len(data):
                group = data[i:i + group_size]
                if all(e.get("Template") == template for e in group):
                    corrected.extend(group)
                    i += group_size
                    continue

        # If no match or incomplete group, convert current entry only
        corrected.append({
            "Template": "OneByOne",
            "TemplateStep": 1,
            "XMLData": entry.get("XMLData"),
            "resizeBars": entry.get("resizeBars")
        })
        i += 1

    return corrected

def assign_template_steps(data):
    final = []
    i = 0

    # Template step rules
    step_sizes = {
        "OneByTwo": 2,
        "TwoByOne": 2,
        "OneByThree": 3,
        "ThreeByOne": 3,
        "TwoByTwo_Col": 4,
        "TwoByTwo": 4,
        "ThreeByTwo": 6,
        "TwoByThree": 6
    }

    while i < len(data):
        entry = data[i]
        template = entry.get("Template")

        if template == "OneByOne":
            final.append({
                "Template": template,
                "TemplateStep": 1,
                "XMLData": entry.get("XMLData"),
                "resizeBars": entry.get("resizeBars")
            })
            i += 1
            continue

        step_size = step_sizes.get(template)
        if step_size and i + step_size - 1 < len(data):
            group = data[i:i + step_size]
            if all(e.get("Template") == template for e in group):
                for step, e in enumerate(group, start=1):
                    final.append({
                        "Template": template,
                        "TemplateStep": step,
                        "XMLData": e.get("XMLData"),
                        "resizeBars": entry.get("resizeBars")
                    })
                i += step_size
            else:
                final.append({
                    "Template": "OneByOne",
                    "TemplateStep": 1,
                    "XMLData": entry.get("XMLData"),
                    "resizeBars": entry.get("resizeBars")
                })
                i += 1
        else:
            final.append({
                "Template": "OneByOne",
                "TemplateStep": 1,
                "XMLData": entry.get("XMLData"),
                "resizeBars": entry.get("resizeBars")
            })
            i += 1

    return final


def copy_empty_pages(goodjson, xlist):
    result = xlist.copy()

    # Extract all empty pages from goodjson
    empty_pages = [entry for entry in goodjson if entry.get("EmptyPage") is True]

    # Track start and end indices
    start_indices = []
    end_indices = []

    for idx, entry in enumerate(goodjson):
        if entry.get("EmptyPage") is True:
            if idx == 0 or (idx > 0 and goodjson[idx - 1].get("EmptyPage") is True and idx - 1 in start_indices):
                start_indices.append(idx)
            elif idx == len(goodjson) - 1 or (idx < len(goodjson) - 1 and goodjson[idx + 1].get("EmptyPage") is True and idx + 1 in end_indices):
                end_indices.append(idx)

    # Handle start empty pages
    for i in sorted(start_indices):
        result.insert(0, {
            "Template": "OneByOne",
            "TemplateStep": 1,
            "XMLData": goodjson[i].get("XMLPageData"),
        })

    # Handle end empty pages
    for i in sorted(end_indices):
        result.append({
            "Template": "OneByOne",
            "TemplateStep": 1,
            "XMLData": goodjson[i].get("XMLPageData")
        })

    # Handle middle empty pages
    for entry in empty_pages:
        idx = goodjson.index(entry)
        if idx in start_indices or idx in end_indices:
            continue  # already handled

        next_entry = goodjson[idx + 1] if idx + 1 < len(goodjson) else None
        if next_entry:
            next_xml = next_entry.get("XMLPageData")
            insert_index = next(
                (i for i, item in enumerate(result) if item.get("XMLData") == next_xml),
                None
            )
            if insert_index is not None:
                result.insert(insert_index, {
                    "Template": "OneByOne",
                    "TemplateStep": 1,
                    "XMLData": entry.get("XMLPageData")
                })

    return result

def add_serialized_index(data):
    for i, entry in enumerate(data, start=0):
        entry["SerializedIndex"] = i
    return data

def add_index(data):
    for i, entry in enumerate(data, start=1):
        entry["Index"] = i
    return data



import xml.etree.ElementTree as ET
import uuid
import re

def CreatePage1(newjson, Index):
    # Find the entry with matching Index
    entry = next((e for e in newjson if e.get("Index") == Index), None)
    if not entry:
        raise ValueError(f"No entry found with Index {Index}")

    template = entry.get("Template")
    serialized_index = entry.get("SerializedIndex")
    raw_xml = entry.get("XMLData", "")

    # Replace any SerializedIndex="..." with the correct value
    raw_xml = re.sub(r'SerializedIndex="[^"]*"', f'SerializedIndex="{serialized_index}"', raw_xml)

    # Parse XMLData into an Element
    try:
        slot_element = ET.fromstring(raw_xml)
    except ET.ParseError as e:
        raise ValueError(f"Invalid XMLData at Index {Index}: {e}")

    # Generate new GUID for the Page
    page_guid = str(uuid.uuid4())

    # Create <Page> element
    page_element = ET.Element("Page", {
        "GUID": page_guid,
        "template": template,
        "IsLocked": "False"
    })

    # Append parsed slot to the page
    page_element.append(slot_element)

    return page_element



def CreatePage2(newjson, Index):
    # Get the current and next entry
    entry1 = next((e for e in newjson if e.get("Index") == Index), None)
    entry2 = next((e for e in newjson if e.get("Index") == Index + 1), None)

    if not entry1 or not entry2:
        raise ValueError(f"Missing entries at Index {Index} and {Index + 1}")

    # Generate new GUID for the Page
    page_guid = str(uuid.uuid4())

    # Create <Page> element with resizeBars from entry1
    page_element = ET.Element("Page", {
        "GUID": page_guid,
        "template": entry1.get("Template"),
        "resizeBars": entry1.get("resizeBars", ""),
        "IsLocked": "False"
    })

    # Normalize template name for logic
    template_type = entry1.get("Template", "").strip()

    # Helper to parse and patch XMLData
    def parse_slot(entry, slot_position, template_type):
        raw_xml = entry.get("XMLData", "")
        serialized_index = entry.get("SerializedIndex")

        # Replace any SerializedIndex="..." with correct value
        raw_xml = re.sub(r'SerializedIndex="[^"]*"', f'SerializedIndex="{serialized_index}"', raw_xml)

        # Parse XML
        try:
            slot_element = ET.fromstring(raw_xml)
        except ET.ParseError as e:
            raise ValueError(f"Invalid XMLData at Index {entry.get('Index')}: {e}")

        # Inject correct resize bar attribute based on slot position and template
        if slot_position == "first":
            if template_type == "OneByTwo":
                slot_element.set("refResizeBarRight", "0")
            elif template_type == "TwoByOne":
                slot_element.set("refResizeBarBottom", "0")
        elif slot_position == "second":
            if template_type == "OneByTwo":
                slot_element.set("refResizeBarLeft", "0")
            elif template_type == "TwoByOne":
                slot_element.set("refResizeBarTop", "0")

        return slot_element

    # First slot: inject correct resize bar
    slot1 = parse_slot(entry1, slot_position="first", template_type=template_type)
    page_element.append(slot1)

    # Second slot: inject correct resize bar
    slot2 = parse_slot(entry2, slot_position="second", template_type=template_type)
    page_element.append(slot2)

    return page_element


def CreatePage3(newjson, Index):
    # Get the three consecutive entries
    entries = [next((e for e in newjson if e.get("Index") == Index + i), None) for i in range(3)]
    if any(e is None for e in entries):
        raise ValueError(f"Missing entries at Index {Index}, {Index+1}, or {Index+2}")

    template = entries[0].get("Template")
    resizeBars = entries[0].get("resizeBars", "")
    page_guid = str(uuid.uuid4())

    # Create <Page> element
    page_element = ET.Element("Page", {
        "GUID": page_guid,
        "template": template,
        "resizeBars": resizeBars,
        "IsLocked": "False"
    })

    # Define resize attributes per slot based on template
    if template == "OneByThree":
        resize_attrs = [
            {"refResizeBarRight": "0"},
            {"refResizeBarLeft": "0", "refResizeBarRight": "1"},
            {"refResizeBarLeft": "1"}
        ]
    elif template == "ThreeByOne":
        resize_attrs = [
            {"refResizeBarBottom": "0"},
            {"refResizeBarTop": "0", "refResizeBarBottom": "1"},
            {"refResizeBarTop": "1"}
        ]
    else:
        raise ValueError(f"Unsupported template type: {template}")

    # Helper to parse and patch XMLData
    def parse_slot(entry, resize_dict):
        raw_xml = entry.get("XMLData", "")
        serialized_index = entry.get("SerializedIndex")

        # Replace any SerializedIndex="..." with correct value
        raw_xml = re.sub(r'SerializedIndex="[^"]*"', f'SerializedIndex="{serialized_index}"', raw_xml)

        # Parse XML
        try:
            slot_element = ET.fromstring(raw_xml)
        except ET.ParseError as e:
            raise ValueError(f"Invalid XMLData at Index {entry.get('Index')}: {e}")

        # Inject resize attributes
        for key, value in resize_dict.items():
            slot_element.set(key, value)

        return slot_element

    # Build and append slots
    for entry, resize_dict in zip(entries, resize_attrs):
        slot = parse_slot(entry, resize_dict)
        page_element.append(slot)

    return page_element



def CreatePage4(newjson, Index):
    # Get four consecutive entries by Index
    entries = [next((e for e in newjson if e.get("Index") == Index + i), None) for i in range(4)]
    if any(e is None for e in entries):
        raise ValueError(f"Missing entries at Index {Index} to {Index + 3}")

    template = entries[0].get("Template")
    resizeBars = entries[0].get("resizeBars", "")
    page_guid = str(uuid.uuid4())

    # Create <Page> element
    page_element = ET.Element("Page", {
        "GUID": page_guid,
        "template": template,
        "resizeBars": resizeBars,
        "IsLocked": "False"
    })

    # Define resize attributes per slot based on template
    if template == "TwoByTwo_Col":
        resize_attrs = [
            {"refResizeBarRight": "0", "refResizeBarBottom": "1"},
            {"refResizeBarRight": "0", "refResizeBarTop": "1"},
            {"refResizeBarLeft": "0", "refResizeBarBottom": "2"},
            {"refResizeBarLeft": "0", "refResizeBarTop": "2"}
        ]
    elif template == "TwoByTwo":
        resize_attrs = [
            {"refResizeBarRight": "1", "refResizeBarBottom": "0"},
            {"refResizeBarLeft": "1", "refResizeBarBottom": "0"},
            {"refResizeBarRight": "2", "refResizeBarTop": "0"},
            {"refResizeBarLeft": "2", "refResizeBarTop": "0"}
        ]
    else:
        raise ValueError(f"Unsupported template type: {template}")

    # Helper to parse and patch XMLData
    def parse_slot(entry, resize_dict):
        raw_xml = entry.get("XMLData", "")
        serialized_index = entry.get("SerializedIndex")

        # Replace any SerializedIndex="..." with correct value
        raw_xml = re.sub(r'SerializedIndex="[^"]*"', f'SerializedIndex="{serialized_index}"', raw_xml)

        # Parse XML
        try:
            slot_element = ET.fromstring(raw_xml)
        except ET.ParseError as e:
            raise ValueError(f"Invalid XMLData at Index {entry.get('Index')}: {e}")

        # Inject resize attributes
        for key, value in resize_dict.items():
            slot_element.set(key, value)

        return slot_element

    # Build and append slots
    for entry, resize_dict in zip(entries, resize_attrs):
        slot = parse_slot(entry, resize_dict)
        page_element.append(slot)

    return page_element


def CreatePage6(newjson, Index):
    # Get six consecutive entries by Index
    entries = [next((e for e in newjson if e.get("Index") == Index + i), None) for i in range(6)]
    if any(e is None for e in entries):
        raise ValueError(f"Missing entries at Index {Index} to {Index + 5}")

    template = entries[0].get("Template")
    resizeBars = entries[0].get("resizeBars", "")
    page_guid = str(uuid.uuid4())

    # Create <Page> element
    page_element = ET.Element("Page", {
        "GUID": page_guid,
        "template": template,
        "resizeBars": resizeBars,
        "IsLocked": "False"
    })

    # Define resize attributes per slot based on template
    if template == "ThreeByTwo":
        resize_attrs = [
            {"refResizeBarRight": "0", "refResizeBarBottom": "1"},
            {"refResizeBarRight": "0", "refResizeBarTop": "1", "refResizeBarBottom": "2"},
            {"refResizeBarRight": "0", "refResizeBarTop": "2"},
            {"refResizeBarLeft": "0", "refResizeBarBottom": "3"},
            {"refResizeBarLeft": "0", "refResizeBarTop": "3", "refResizeBarBottom": "4"},
            {"refResizeBarLeft": "0", "refResizeBarTop": "4"}
        ]
    elif template == "TwoByThree":
        resize_attrs = [
            {"refResizeBarRight": "1", "refResizeBarBottom": "0"},
            {"refResizeBarLeft": "1", "refResizeBarRight": "2", "refResizeBarBottom": "0"},
            {"refResizeBarLeft": "2", "refResizeBarBottom": "0"},
            {"refResizeBarRight": "3", "refResizeBarTop": "0"},
            {"refResizeBarLeft": "3", "refResizeBarRight": "4", "refResizeBarTop": "0"},
            {"refResizeBarLeft": "4", "refResizeBarTop": "0"}
        ]
    else:
        raise ValueError(f"Unsupported template type: {template}")

    # Helper to parse and patch XMLData
    def parse_slot(entry, resize_dict):
        raw_xml = entry.get("XMLData", "")
        serialized_index = entry.get("SerializedIndex")

        # Replace any SerializedIndex="..." with correct value
        raw_xml = re.sub(r'SerializedIndex="[^"]*"', f'SerializedIndex="{serialized_index}"', raw_xml)

        # Parse XML
        try:
            slot_element = ET.fromstring(raw_xml)
        except ET.ParseError as e:
            raise ValueError(f"Invalid XMLData at Index {entry.get('Index')}: {e}")

        # Inject resize attributes
        for key, value in resize_dict.items():
            slot_element.set(key, value)

        return slot_element

    # Build and append slots
    for entry, resize_dict in zip(entries, resize_attrs):
        slot = parse_slot(entry, resize_dict)
        page_element.append(slot)

    return page_element

def CheckParents(pages_element):
    """
    Ensures each <Text> element has a ParentGUID matching its containing <Page> GUID.
    Modifies the XML tree in-place.
    """
    for page in pages_element.findall("Page"):
        page_guid = page.get("GUID")
        for slot in page.findall("Slot"):
            for text in slot.findall("Text"):
                current_parent = text.get("ParentGUID")
                if current_parent != page_guid:
                    print(f"Fixing ParentGUID: {current_parent} → {page_guid}")
                    text.set("ParentGUID", page_guid)


def generate_pages(newjson):
    pages = ET.Element("Pages")
    i = 0
    while i < len(newjson):
        entry = newjson[i]
        template = entry.get("Template")
        index = entry.get("Index")

        # Normalize template name for matching
        template_upper = template.strip().upper()

        if template_upper == "ONEBYONE":
            page = CreatePage1(newjson, index)
            pages.append(page)
            i += 1

        elif template_upper in ["ONEBYTWO", "TWOBYONE"]:
            page = CreatePage2(newjson, index)
            pages.append(page)
            i += 2

        elif template_upper in ["ONEBYTHREE", "THREEBYONE"]:
            page = CreatePage3(newjson, index)
            pages.append(page)
            i += 3

        elif template_upper in ["TWOBYTWO", "TWOBYTWO_COL"]:
            page = CreatePage4(newjson, index)
            pages.append(page)
            i += 4

        elif template_upper in ["THREEBYTWO", "TWOBYTHREE"]:
            page = CreatePage6(newjson, index)
            pages.append(page)
            i += 6

        else:
            print(f"Unknown template: {template} at index {i}")
            i += 1  # Skip unknown template safely


    CheckParents(pages)

    return pages

import xml.dom.minidom as minidom
import xml.etree.ElementTree as ET

def pretty_print_xml(element):
    rough_string = ET.tostring(element, encoding='unicode')
    reparsed = minidom.parseString(rough_string)
    return reparsed.toprettyxml(indent="  ")



def create_new_ins_file(backupjson, brokenjson, backupfilepath):
    new_root =""

    with zipfile.ZipFile(backupfilepath, 'r') as zip_ref:
        contents = zip_ref.namelist()
        if "model.ins" in contents:
            with zip_ref.open("model.ins") as ins_file:
                   try:
                           xml_data = ins_file.read().decode("utf-8")
                           
                           #copy page setup data from the backup ins file
                           
                           root = ET.fromstring(xml_data)
                           global_setting = root.find("GlobalSetting")
                           if global_setting is None:
                                return "parse error"

                           new_root = ET.Element("Instruction")
                           new_root.append(global_setting)
              
                           goodjson = backupjson.get("data", [])
                           badjson = brokenjson.get("data", [])
                           newjson = []
                           index = 1
                           LastBrickGoodIndex = -1
                           LastBrickBadIndex = -1
                           # parse the json of the file with the corrupted ins data

                           for entry in badjson:
                                page_step = entry.get("PageStep")
                                uuids = entry.get("uuids", [])
                                itemnos = entry.get("itemNos", []) 
                                emptypage = entry.get("EmptyPage")
                               
                                if not uuids and not itemnos: # empty step found , see if we can match it, based on the last brick found.

                                    if not emptypage is None:     #skip instruction pages
                                        if emptypage == True:
                                           index +=1
                                           continue

                                    # Search the good data for the last found brick and see if then next brick(s) also has an empty slot
                                    found = False
                                    if LastBrickGoodIndex > 0 and LastBrickBadIndex > 0:
                                        IndexDif = index - LastBrickBadIndex
                                        GoodIndex = LastBrickGoodIndex + IndexDif

                                        for findempty in goodjson:
                                            if findempty.get("counter") == GoodIndex:
                                                uuids = findempty.get("uuids", [])
                                                itemnos = findempty.get("itemNos", []) 
                                                if not uuids and not itemnos:  # its empty, copy instead of empty block
                                                        Template = findempty.get("Template")
                                                        TemplateStep = findempty.get("TemplateStep")
                                                        if  TemplateStep is None: TemplateStep = 1
                                                        XMLData = findempty.get("XMLPageData")
                                                        resizeBars = findempty.get("resizeBars")
                                                        if  resizeBars is None: resizeBars = "None"
                                                        found = True
                                                        break


                                    # Create an empty step if uuids and itemnos are emtpy and previous block cannot be matched 
                                    if found == False: 
                                        Template = "OneByOne"                                    
                                        TemplateStep = 1
                                        XMLData =ET.tostring( create_default_step(index), encoding='unicode')
                                        resizeBars = "None"
                                else:

                                    # Find matching steps by uuids or itemnos in the good data

                                    CountNumber = FindStep(goodjson, page_step, uuids, itemnos)
                                    

                                    if CountNumber == -1:       # create an new step if data could not be found
                                        Template = "OneByOne"                                    
                                        TemplateStep = 1
                                        XMLData =ET.tostring( create_default_step(index), encoding='unicode')
                                        resizeBars = "None"
                                    else :
                                        
                                        for entry in goodjson:
                                            if entry.get("counter") == CountNumber:

                                                LastBrickGoodIndex = CountNumber      # save the last brick counter to match empty bricks
                                                LastBrickBadIndex = index

                                                Template = entry.get("Template")
                                                TemplateStep = entry.get("TemplateStep")
                                                if  TemplateStep is None: TemplateStep = 1
                                                XMLData = entry.get("XMLPageData")
                                                resizeBars = entry.get("resizeBars")
                                                if  resizeBars is None: resizeBars = "None"
                                                break
                                                # Add the block to the list

                                newjson.append({
                                    "Template": Template,
                                    "TemplateStep": TemplateStep,
                                    "XMLData":  XMLData,
                                    "resizeBars": resizeBars
                                    })

                                index +=1
                           
                                
                           # print(json.dumps(newjson , indent=2))

                           newjson = correct_templates(newjson)
                           newjson = assign_template_steps(newjson)

                           # create a serialized index over the file

                           newjson = add_serialized_index(newjson)

                           # add empty pages from the backupfile

                           newjson = copy_empty_pages(goodjson, newjson)

                            # create an extra index over the file

                           newjson = add_index(newjson)
                           
                           print(json.dumps(newjson , indent=2))
                        

                           pages = generate_pages(newjson)
                           new_root.append(pages)


                           content_setting = root.find("ContentItems")
                           if not content_setting is None:
                                new_root.append(content_setting)


                           CustomLayouts_setting = root.find("CustomLayouts")
                           if not content_setting is None:
                                new_root.append(CustomLayouts_setting)

                           print(pretty_print_xml(new_root))




                           
                   except ET.ParseError as e:
                       return "xml error"

    return new_root



def select_backup():
    path = filedialog.askopenfilename(title="Select Backup File", filetypes=[("Studio Files", "*.io")])
    if path:
        selected_backup_path.set(path)

def select_broken_studio_file():
    path = filedialog.askopenfilename(title="Select Broken Studio File", filetypes=[("Studio Files", "*.io")])
    if path:
        broken_path.set(path)

def fix_studio_file():
    fixed_path.set("Fixing studio file")

    backuppath = Path(selected_backup_path.get())
    if not backuppath.is_file():
        fixed_path.set("No Backup Studio file selected.")
        return

    brokenio_path = Path(broken_path.get())
    if not brokenio_path.is_file():
        fixed_path.set("No Studio file to fix.")
        return

    backupjson = unpack_and_parse_io(backuppath)

    create_ins_file = True

    if backupjson.get("status") == "error":
        errormsg = "⚠️ Parsing backup failed: "+ backupjson.get("message")
        fixed_path.set(errormsg)
        create_ins_file = False
    else:

        brokenjson = unpack_and_parse_io(brokenio_path)
        if brokenjson.get("status") == "error":
            errormsg = "⚠️ Parsing corrupted file failed: "+ backupjson.get("message")
            fixed_path.set(errormsg)
            create_ins_file = False

    #creating new ins file
    if create_ins_file:
        # Generate new XML content
        new_xml = create_new_ins_file(backupjson, brokenjson, backuppath)

        # Convert ElementTree.Element to string if needed
        if isinstance(new_xml, ET.Element):
            new_xml = ET.tostring(new_xml, encoding="utf-8", method="xml")
        elif isinstance(new_xml, tk.StringVar):
            new_xml = new_xml.get().encode("utf-8")
        elif isinstance(new_xml, str):
            new_xml = new_xml.encode("utf-8")

        # Generate new filename
        base, ext = os.path.splitext(brokenio_path)
        rfixed_path = f"{base}_fixed{ext}"

        # Read original zip and write to new zip
        with zipfile.ZipFile(brokenio_path, 'r') as zin:
            with zipfile.ZipFile(rfixed_path, 'w') as zout:
                for item in zin.infolist():
                    if item.filename != "model.ins":
                        data = zin.read(item.filename)
                        zout.writestr(item.filename, data)
                zout.writestr("model.ins", new_xml)

        print(f"✅ Fixed .io file created: {rfixed_path}")
        fixed_path.set(f"{os.path.basename(rfixed_path)} created successfully.")


import tkinter as tk
import webbrowser

def open_help_window():
    help_win = tk.Toplevel()
    help_win.title("Help")
    help_win.geometry("1000x400")

    text_widget = tk.Text(help_win, wrap="word", padx=10, pady=10)
    text_widget.pack(fill="both", expand=True)

    help_text = (
        "🧰 LEGO Studio File Utility Help\n\n"
        "- Select a .io file to begin.\n"
        "- Press Create backup to make a backup.\n"
        "- Enabled autobackup will check every few minutes if the save-file has changed, if it has changed it will save a backup.\n"
        "- Backups are stored in the 'IObackups' folder next to your original file.\n\n"
        "Lego studio will often corrupt or destroy your instructions if you make major changes to your lego build.\n"
        "With this app, you can recover your instructions if studio corrupted it.\n"
        "In the repair section, select the most recent backup-file that has correct instructions\n"
        "Then select your latest file with the corrupted instructions.\n"
        "When the fix button is pressed, this app will attempt to recreate the instructions with the data from the backup.\n"
        "The original file will not be overwritten, but a new fixed file will be created, with hopefully a lot of the instructions restored.\n\n"
        "If you like this app, please follow me on rebrickable:\n"
    )

    text_widget.insert("end", help_text)

    # Insert the link text
    coffee_link = "https://rebrickable.com/users/Terraxz/mocs/"
    link_text = coffee_link + "\n"
    text_widget.insert("end", link_text)

    # Calculate tag range correctly
    line_start = text_widget.search(coffee_link, "1.0", tk.END)
    line_end = f"{line_start}+{len(coffee_link)}c"

    # Apply tag styling and click behavior
    text_widget.tag_add("coffee_link", line_start, line_end)
    text_widget.tag_config("coffee_link", foreground="blue", underline=True)
    text_widget.tag_bind("coffee_link", "<Button-1>", lambda e: webbrowser.open(coffee_link))

    # Lock the widget
    text_widget.config(state="disabled")


last_modified_time = None
autosave_thread = None
stop_autosave = threading.Event()

def start_autosave_monitor():
    global autosave_thread, last_modified_time
    stop_autosave.clear()

    def monitor():
        global last_modified_time
        while not stop_autosave.is_set():
            if autobackup_var.get():
                path = Path(studio_path.get())
                if path.is_file():
                    current_mtime = path.stat().st_mtime
                    if last_modified_time is None:
                        last_modified_time = current_mtime
                    elif current_mtime != last_modified_time:
                        last_modified_time = current_mtime
                        create_backup()
            interval = interval_var.get()
            time.sleep(max(60, interval * 60))  # minimum 1 minute

    autosave_thread = threading.Thread(target=monitor, daemon=True)
    autosave_thread.start()



def on_close(window):
    stop_autosave.set()  # stop the autosave thread
    window.destroy()     # close the GUI


# ─────────────────────────────────────────────
# 🧱 Initialization
# ─────────────────────────────────────────────

def init_gui():
    global studio_path, backup_path, broken_path, selected_backup_path, fixed_path, autobackup_var, interval_var

  
    window = tk.Tk()
    window.title("Lego Studio File Utility")
    window.geometry("500x450")

    # Initialize path variables
    studio_path = tk.StringVar()
    backup_path = tk.StringVar()
    broken_path = tk.StringVar()
    selected_backup_path = tk.StringVar()
    fixed_path = tk.StringVar()
    autobackup_var = tk.BooleanVar()
    interval_var = tk.IntVar()

    build_panels(window)

    # Load saved values
    studio_path.set(load_config("path", ""))
    autobackup_var.set(load_config("autocheck", False))
    interval_var.set(load_config("interval", 10))

    # Auto-save when values change
    autobackup_var.trace_add("write", lambda *args: save_config("autocheck", autobackup_var.get()))
    interval_var.trace_add("write", lambda *args: save_config("interval", interval_var.get()))
    studio_path.trace_add("write", lambda *args: save_config("path", studio_path.get()))

    window.protocol("WM_DELETE_WINDOW", lambda: on_close(window))
    start_autosave_monitor()

    window.mainloop()

# ─────────────────────────────────────────────
# 🖼️ GUI Panels
# ─────────────────────────────────────────────

default_button_font = ("Arial", 9)
default_button_padx = 2
default_button_pady = 2


def build_panels(window):
    global backup_listbox

    default_button_font = ("Arial", 9)

    # Create a container frame for vertical layout
    container = tk.Frame(window)
    container.pack(fill="both", expand=True, padx=10, pady=5)
    container.rowconfigure(0, weight=1)
    container.rowconfigure(1, weight=1)
    container.columnconfigure(0, weight=1)

    # ─────────────────────────────────────────────
    # 🧱 Frame 1: Backup Tools (Top)
    # ─────────────────────────────────────────────
    frame1 = tk.LabelFrame(container, text="Part 1: Backup Tools", padx=10, pady=10)
    frame1.grid(row=0, column=0, sticky="nsew", pady=(0, 5))

    tk.Button(frame1, text="Select Studio File", command=select_studio_file,
              anchor="w", font=default_button_font).pack(fill="x", pady=2)
    tk.Label(frame1, textvariable=studio_path, anchor="w", fg="blue").pack(fill="x")

    tk.Button(frame1, text="Create Backup", command=create_backup,
              anchor="w", font=default_button_font).pack(fill="x", pady=2)
    tk.Label(frame1, textvariable=backup_path, anchor="w", fg="blue").pack(fill="x")

    # Autobackup checkbox and interval entry
    autobackup_frame = tk.Frame(frame1)
    autobackup_frame.pack(fill="x", pady=(5, 0))

    tk.Checkbutton(autobackup_frame, variable=autobackup_var).pack(side="left")

    tk.Label(autobackup_frame, text="Autobackup every").pack(side="left", padx=(5, 0))

    tk.Entry(autobackup_frame, textvariable=interval_var, width=5).pack(side="left", padx=(5, 0))

    tk.Label(autobackup_frame, text="minutes").pack(side="left")

    # ─────────────────────────────────────────────
    # 🛠️ Frame 2: Repair Tools (Bottom)
    # ─────────────────────────────────────────────
    frame2 = tk.LabelFrame(container, text="Part 2: Repair Tools", padx=10, pady=10)
    frame2.grid(row=1, column=0, sticky="nsew", pady=(5, 0))

    tk.Button(frame2, text="Select Backup", command=select_backup,
              anchor="w", font=default_button_font).pack(fill="x", pady=2)
    tk.Label(frame2, textvariable=selected_backup_path, anchor="w", fg="blue").pack(fill="x")

    tk.Button(frame2, text="Select Corrupted Studio File", command=select_broken_studio_file,
              anchor="w", font=default_button_font).pack(fill="x", pady=2)
    tk.Label(frame2, textvariable=broken_path, anchor="w", fg="blue").pack(fill="x")

    tk.Button(frame2, text="Fix Studio File", command=fix_studio_file,
              anchor="w", font=default_button_font).pack(fill="x", pady=2)
    tk.Label(frame2, textvariable=fixed_path, anchor="w", fg="blue").pack(fill="x")

    

    # ❓ Help button in bottom-right
    help_button = tk.Button(window, text=" Help ", command=open_help_window,
                            font=("Arial", 10), padx=1, pady=1)
    help_button.place(relx=0.50, rely=0.98, anchor="se")


# ─────────────────────────────────────────────
# 🚀 Launch
# ─────────────────────────────────────────────

if __name__ == "__main__":
    init_gui()