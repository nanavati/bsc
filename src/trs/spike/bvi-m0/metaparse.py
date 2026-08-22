#!/usr/bin/env python3
"""M0 versioned Verilator metadata adapter.

Extracts, from a verilated model's frontend dump, the facts the BVI link
step needs: top-module ports (verilator name, origName, direction, width,
pinIndex), parameters, timescale, and the presence of delays or DPI.

Two formats, selected by probing the verilator binary:
  - XML  (--xml-only): present through 5.045 (distro 5.020 uses this).
  - JSON (--json-only): the replacement from 5.046 onward.
The adapter returns one normalized dict either way; nothing downstream
may look at the raw dump.
"""
import json
import re
import subprocess
import sys
from pathlib import Path


def verilator_version(vlt):
    out = subprocess.run([vlt, "--version"], capture_output=True, text=True).stdout
    m = re.search(r"Verilator (\d+)\.(\d+)", out)
    return (int(m.group(1)), int(m.group(2))) if m else (0, 0)


def pick_format(vlt):
    maj, minor = verilator_version(vlt)
    return "xml" if (maj, minor) < (5, 46) else "json"


def run_dump(vlt, top, sources, ydirs, defines, mdir, fmt):
    cmd = [vlt, "--cc", "--no-timing", f"--{fmt}-only",
           "--top-module", top, "-Mdir", str(mdir)]
    for d in ydirs:
        cmd += ["-y", str(d)]
    for k, v in (defines or {}).items():
        cmd += [f"-D{k}={v}" if v is not None else f"-D{k}"]
    cmd += [str(s) for s in sources]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"verilator {fmt} dump failed:\n{r.stderr}")
    return mdir


def _parse_xml(path, top):
    text = Path(path).read_text()
    widths = {}
    for m in re.finditer(r"<basicdtype [^>]*>", text):
        attrs = dict(re.findall(r'(\w+)="([^"]*)"', m.group(0)))
        if "left" in attrs:
            widths[attrs["id"]] = abs(int(attrs["left"]) - int(attrs["right"])) + 1
        else:
            widths[attrs["id"]] = 1
    # scope to the top module element
    mods = re.split(r"(?=<module )", text)
    ports, params = [], {}
    found_top = False
    for chunk in mods:
        head = re.match(r'<module [^>]*name="([^"]*)"[^>]*>', chunk)
        if not head or head.group(1) != top:
            continue
        found_top = True
        for vm in re.finditer(r"<var [^>]*>", chunk):
            attrs = dict(re.findall(r'(\w+)="([^"]*)"', vm.group(0)))
            if "dir" in attrs:
                ports.append({
                    "name": attrs["name"],
                    "orig_name": attrs.get("origName", attrs["name"]),
                    "dir": attrs["dir"],
                    "width": widths.get(attrs.get("dtype_id"), 1),
                    "pin_index": int(attrs.get("pinIndex", "0")),
                })
            elif attrs.get("param") == "true" or attrs.get("vartype") == "parameter":
                params[attrs.get("origName", attrs["name"])] = attrs.get("value")
    if not found_top:
        raise RuntimeError(f"top module {top!r} not found in XML dump")
    has_delay = "<delay" in text or 'name="#' in text
    has_dpi = "dpiImport" in text or "dpiExport" in text or 'dpi="' in text
    ts = re.search(r'timeprecision="([^"]*)"', text)
    return {"format": "xml", "ports": ports, "params": params,
            "has_delay": has_delay, "has_dpi": has_dpi,
            "timeprecision": ts.group(1) if ts else None}


def _walk_json(node, fn):
    if isinstance(node, dict):
        fn(node)
        for v in node.values():
            _walk_json(v, fn)
    elif isinstance(node, list):
        for v in node:
            _walk_json(v, fn)


def _parse_json(path, top):
    tree = json.loads(Path(path).read_text())
    ports, params = [], {}
    state = {"in_top": False, "has_delay": False, "has_dpi": False,
             "timeprecision": None, "found_top": False}
    # JSON tree: nodes carry "type" ("MODULE", "VAR", ...); VARs under the
    # top MODULE with a direction are ports.  Field names verified against
    # the built 5.050 in the M0 gate (see driver.py --check-adapter).
    def visit_module(mod):
        if mod.get("type") != "MODULE" or mod.get("name") != top:
            return
        state["found_top"] = True
        def visit(n):
            if not isinstance(n, dict):
                return
            t = n.get("type")
            if t == "VAR":
                direction = n.get("direction") or n.get("dir")
                if direction and direction not in ("NONE", ""):
                    ports.append({
                        "name": n.get("name"),
                        "orig_name": n.get("origName", n.get("name")),
                        "dir": direction.lower(),
                        "width": _json_width(n),
                        "pin_index": int(n.get("pinIndex", 0) or 0),
                    })
                elif n.get("isParam") or n.get("varType") == "GPARAM":
                    params[n.get("origName", n.get("name"))] = n.get("value")
            if t in ("DELAY", "TIMINGCONTROL"):
                state["has_delay"] = True
            if t in ("CFUNC",) and n.get("dpiImport"):
                state["has_dpi"] = True
        _walk_json(mod, visit)
    _walk_json(tree, visit_module)
    if not state["found_top"]:
        raise RuntimeError(f"top module {top!r} not found in JSON dump")
    return {"format": "json", "ports": ports, "params": params,
            "has_delay": state["has_delay"], "has_dpi": state["has_dpi"],
            "timeprecision": state["timeprecision"]}


def _json_width(n):
    dt = n.get("dtype") or {}
    if isinstance(dt, dict) and "left" in dt and dt["left"] is not None:
        return abs(int(dt["left"]) - int(dt["right"])) + 1
    rng = n.get("range") or ""
    m = re.match(r"\[(\d+):(\d+)\]", str(rng))
    if m:
        return abs(int(m.group(1)) - int(m.group(2))) + 1
    return 1


def extract(vlt, top, sources, ydirs=(), defines=None, workdir="obj_meta"):
    fmt = pick_format(vlt)
    mdir = Path(workdir)
    mdir.mkdir(parents=True, exist_ok=True)
    run_dump(vlt, top, sources, ydirs, defines, mdir, fmt)
    if fmt == "xml":
        dumps = list(mdir.glob("*.xml"))
    else:
        dumps = [p for p in mdir.glob("*.tree.json")] or list(mdir.glob("*.json"))
    if not dumps:
        raise RuntimeError(f"no {fmt} dump produced in {mdir}")
    parse = _parse_xml if fmt == "xml" else _parse_json
    return parse(dumps[0], top)


if __name__ == "__main__":
    vlt, top = sys.argv[1], sys.argv[2]
    meta = extract(vlt, top, sys.argv[3:])
    json.dump(meta, sys.stdout, indent=2)
    print()
