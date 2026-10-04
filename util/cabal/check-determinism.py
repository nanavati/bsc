#!/usr/bin/env python3
"""Compare clean parallel, serial, and incremental Cabal build products.

Uses one dedicated build directory so absolute build paths do not change.
External dependencies in the Cabal store are reused. This checks local
objects, interfaces, and every executable/test binary recorded in plan.json.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[2]
SUFFIXES = {".o", ".hi", ".dyn_o", ".dyn_hi", ".p_o", ".p_hi",
            ".a", ".so", ".dylib", ".dll"}


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def snapshot(builddir):
    files = {p for p in (builddir / "build").rglob("*")
             if p.is_file() and (p.suffix in SUFFIXES or ".so." in p.name)}
    plan = json.loads((builddir / "cache/plan.json").read_text())
    binaries = 0
    for package in plan["install-plan"]:
        if package.get("style") != "local":
            continue
        components = package.get("components", {"component": package})
        for component in components.values():
            if component.get("bin-file"):
                binary = Path(component["bin-file"])
                if not binary.is_file():
                    raise RuntimeError(f"declared binary was not built: {binary}")
                files.add(binary)
                binaries += 1
    if not files or not binaries:
        raise RuntimeError("build plan contains no local objects or binaries")
    return {str(p.relative_to(builddir)): digest(p) for p in sorted(files)}


def marker_interface_groups(builddir, products, marker, module):
    """Associate the shared test source with every plan-recorded test runner."""
    endings = tuple("/" + module.replace(".", "/") + suffix
                    for suffix in (".hi", ".dyn_hi", ".p_hi"))
    interfaces = sorted(name for name in products if name.endswith(endings))
    if marker == (ROOT / "testsuite/RunTests.hs").resolve():
        plan = json.loads((builddir / "cache/plan.json").read_text())
        groups = {}
        for package in plan["install-plan"]:
            if package.get("style") != "local" or package["pkg-name"] != "bsc":
                continue
            components = package.get("components", {package.get("component-name", ""): package})
            for name, component in components.items():
                if not name.startswith("test:"):
                    continue
                binary = component.get("bin-file")
                if not binary:
                    raise RuntimeError(f"no binary path recorded for marker component {name}")
                prefix = str(Path(binary).parent.relative_to(builddir)) + "/"
                groups[name] = [path for path in interfaces if path.startswith(prefix)]
        if not groups:
            raise RuntimeError(f"no test runners recorded for marker source {marker}")
    else:
        groups = {module: interfaces}
    for component, paths in groups.items():
        if not paths:
            raise RuntimeError(f"no compiled interface for marker {marker} in {component}")
    return groups


def assert_marker_edits(builddir, baseline, edited, marker_modules):
    observed = {}
    for marker, module in marker_modules.items():
        groups = marker_interface_groups(builddir, baseline, marker, module)
        observed[str(marker.relative_to(ROOT))] = groups
        for component, interfaces in groups.items():
            stale = [name for name in interfaces
                     if name not in edited or edited[name] == baseline[name]]
            if stale:
                raise RuntimeError(f"source edit did not change every interface for {marker} "
                                   f"in {component}: {', '.join(stale)}")
    return observed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--builddir", default="dist-determinism")
    parser.add_argument("--output", default="determinism-results")
    parser.add_argument("--jobs", type=int, nargs="+", default=[1, 16, 64, 64, 64],
                        metavar="N", help="clean-build worker counts, in order; repeats are intentional")
    parser.add_argument("--marker", action="append",
                        help="tracked source to edit/revert; repeat for several components")
    args = parser.parse_args()
    if len(args.jobs) < 2 or any(jobs < 1 for jobs in args.jobs):
        parser.error("--jobs needs at least two positive worker counts")
    ghc_version = subprocess.check_output(["ghc", "--numeric-version"], text=True).strip()
    if tuple(map(int, ghc_version.split("."))) < (9, 14, 1):
        parser.error("determinism checks require GHC 9.14.1 or newer")
    builddir = (ROOT / args.builddir).resolve()
    if builddir == ROOT or ROOT not in builddir.parents:
        parser.error("--builddir must be a dedicated directory inside this checkout")
    owner = builddir / ".determinism-check"
    if builddir.exists() and not owner.exists():
        parser.error(f"refusing to clean existing unmarked directory: {builddir}")
    builddir.mkdir(parents=True, exist_ok=True)
    owner.touch()
    output = (ROOT / args.output / time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())).resolve()
    output.mkdir(parents=True, exist_ok=False)
    markers = [(ROOT / name).resolve() for name in
               (args.marker or ["src/comp/Bag.hs", "src/comp/app/bsc.hs", "testsuite/RunTests.hs"])]
    for marker in markers:
        if ROOT not in marker.parents or not marker.is_file() or marker.suffix != ".hs":
            parser.error(f"marker must be an existing .hs source in this checkout: {marker}")
    marker_modules = {}
    for marker in markers:
        declaration = re.search(r"^\s*module\s+([A-Z][\w.']*)", marker.read_text(), re.MULTILINE)
        marker_modules[marker] = declaration.group(1) if declaration else "Main"
    command = ["cabal", "build", "all", f"--builddir={builddir}", "--enable-tests"]
    # Cabal monitors configuration flags, not ambient environment changes.
    for variable, flag in (("NOGIT", "no-git"),
                           ("NOUPDATEBUILDVERSION", "no-update-build-version"),
                           ("STP_STUB", "stp-stub"),
                           ("YICES_STUB", "yices-stub")):
        value = os.environ.get(variable, "")
        enabled = bool(value) if variable.endswith("_STUB") else value == "1"
        command.append("--flags=" + ("" if enabled else "-") + flag)
    (output / "configuration.json").write_text(json.dumps({
        "command": command, "job_counts": args.jobs,
        "markers": [str(p.relative_to(ROOT)) for p in markers],
        "revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "ghc": ghc_version,
        "cabal": subprocess.check_output(["cabal", "--numeric-version"], text=True).strip(),
        "version_environment": {key: os.environ.get(key) for key in
                                ("NOGIT", "NOUPDATEBUILDVERSION")},
    }, indent=2) + "\n")

    def build(name, jobs, clean=False):
        if clean:
            for child in ("build", "cache", "packagedb", "tmp"):
                directory = builddir / child
                if directory.exists():
                    shutil.rmtree(directory)
        logfile = output / f"{name}.log"
        print(f"{name}: building with {jobs} jobs; log {logfile}", flush=True)
        start = time.monotonic()
        with logfile.open("w") as log:
            subprocess.run(command + [f"-j{jobs}", f"--ghc-options=-j{jobs}"],
                           cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
        hashes = snapshot(builddir)
        (output / f"{name}.json").write_text(json.dumps(hashes, indent=2) + "\n")
        print(f"{name}: {len(hashes)} products, {time.monotonic() - start:.0f}s", flush=True)
        return hashes

    failures = []

    def compare(name, expected, actual):
        different = sorted(p for p in expected.keys() | actual.keys()
                           if expected.get(p) != actual.get(p))
        (output / f"differences-{name}.txt").write_text("".join(p + "\n" for p in different))
        print(f"{name}: {'FAIL: ' + str(len(different)) + ' differing products' if different else 'PASS'}",
              flush=True)
        if different:
            failures.append(name)

    baseline = None
    for index, jobs in enumerate(args.jobs, 1):
        name = f"clean-{index:02d}-j{jobs}"
        products = build(name, jobs, clean=True)
        if baseline is None:
            baseline = products
        else:
            compare(name, baseline, products)
    incremental_jobs = args.jobs[-1]
    original = {p: p.read_bytes() for p in markers}
    try:
        for marker, contents in original.items():
            # A comment need not change any products, even after recompilation.
            # Change a recorded optimization setting so an ignored source edit
            # cannot accidentally pass the incremental check.
            marker.write_bytes(b"{-# OPTIONS_GHC -fno-cse #-}\n" + contents)
        edited = build("edited", incremental_jobs)
        observed = assert_marker_edits(builddir, baseline, edited, marker_modules)
        (output / "edited-marker-interfaces.json").write_text(
            json.dumps(observed, indent=2) + "\n")
    finally:
        for marker, contents in original.items():
            marker.write_bytes(contents)
    compare("reverted", baseline, build("reverted", incremental_jobs))
    print(f"{'FAIL' if failures else 'PASS'}: results in {output}")
    return bool(failures)


if __name__ == "__main__":
    # Let the source-restoration finally block run when a job is cancelled.
    signal.signal(signal.SIGTERM, lambda number, frame: sys.exit(128 + number))
    try:
        sys.exit(main())
    except (RuntimeError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
