#!/usr/bin/env python3
"""Exact f092-vs-component parity checks, using one stable working path.

No compiler is invoked until this script is explicitly run with both binary
folders. Snapshots are retained in a temporary directory by default. Every case
runs the old compiler first and the structural compiler second with the same
working directory, source files, output names, runtime directory, and flags.
"""
from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass


@dataclass(frozen=True)
class Case:
    name: str
    source: str
    options: tuple[str, ...]
    required: tuple[str, ...]
    expected_failure: bool = False
    simulate: bool = False


CASES = (
    Case("verilog", "SplitScheduleFeatures.bsv", ("-verilog", "-elab"),
         ("SplitScheduleFeatures.bo", "sysSplitScheduleFeatures.ba",
          "mkSplitSlot.ba", "module_splitAddThree.ba", "sysSplitScheduleFeatures.v")),
    Case("verilog-embedded", "SplitScheduleFeatures.bsv",
         ("-verilog", "-elab", "-elab-verilog"),
         ("SplitScheduleFeatures.bo", "sysSplitScheduleFeatures.ba",
          "mkSplitSlot.ba", "module_splitAddThree.ba", "sysSplitScheduleFeatures.v")),
    Case("schedule-error", "SplitScheduleError.bsv", ("-verilog", "-elab"),
         ("sysSplitScheduleError.ba",), expected_failure=True),
    Case("foreign", "ForeignMetadata.bsv", ("-verilog", "-elab"),
         ("ForeignMetadata.bo", "metadata_add.ba", "mkForeignMetadata.ba",
          "mkForeignMetadata.v")),
    Case("bluesim", "SplitScheduleFeatures.bsv", ("-sim", "-elab"),
         ("SplitScheduleFeatures.bo", "sysSplitScheduleFeatures.ba",
          "mkSplitSlot.ba", "module_splitAddThree.ba", "sysSplitScheduleFeatures.cxx",
          "sysSplitScheduleFeatures.h"), simulate=True),
)
COMMON = ("-no-show-timestamps", "-no-show-version")
ARTIFACT_SUFFIXES = {".bo", ".ba", ".v", ".cxx", ".h", ".c"}
EXPECTED_SIMULATION = b"split-features: 6 16 10\n"
# Four update cycles yield shared=1+2+1+2, marks=3+5+3+5; slot receives
# (0+3)+1 and (2+3)+1 on even cycles and is consumed on following odd cycles.


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run_command(argv: list[str], cwd: Path, env: dict[str, str], log: Path,
                timeout: int) -> subprocess.CompletedProcess:
    completed = subprocess.run(argv, cwd=cwd, env=env, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, timeout=timeout)
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_bytes(completed.stdout)
    return completed


def reset_work(work: Path, fixtures: Path) -> None:
    # Refuse broad or repository-root deletion: this harness owns one directory.
    if not work.name.startswith("component-parity-work"):
        raise ValueError("--work basename must start with component-parity-work")
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    for source in fixtures.glob("*.bsv"):
        shutil.copyfile(source, work / source.name)


def snapshot_files(work: Path, destination: Path) -> dict[str, dict]:
    files = {}
    for path in sorted(work.rglob("*")):
        if not path.is_file() or path.suffix not in ARTIFACT_SUFFIXES:
            continue
        relative = path.relative_to(work)
        output = destination / relative
        output.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, output)
        contents = output.read_bytes()
        files[str(relative)] = {"bytes": len(contents), "sha256": digest(contents)}
    return files


def run_case(case: Case, label: str, bins: Path, args, env_base: dict) -> dict:
    reset_work(args.work, args.fixtures)
    destination = args.results / case.name / label
    destination.mkdir(parents=True)
    env = dict(env_base)
    env["PATH"] = str(bins) + os.pathsep + env.get("PATH", "")
    env["BSC"] = str(bins / "bsc")
    env["BLUETCL"] = str(bins / "bluetcl")
    command = [str(bins / "bsc"), *COMMON, "-u", *case.options, case.source]
    commands = [{"argv": command, "log": "compile.log"}]
    compile_result = run_command(command, args.work, env, destination / "compile.log", args.timeout)
    commands[-1]["returncode"] = compile_result.returncode
    failures = []
    if (compile_result.returncode != 0) != case.expected_failure:
        failures.append("unexpected compile return code " + str(compile_result.returncode))
    runtime_output = None
    if case.simulate and compile_result.returncode == 0:
        command = [str(bins / "bsc"), *COMMON, "-sim", "-e",
                   "sysSplitScheduleFeatures", "-o", "feature-sim"]
        commands.append({"argv": command, "log": "link.log"})
        linked = run_command(command, args.work, env, destination / "link.log", args.timeout)
        commands[-1]["returncode"] = linked.returncode
        if linked.returncode != 0:
            failures.append("simulation link failed")
        else:
            command = [str(args.work / "feature-sim")]
            commands.append({"argv": command, "log": "runtime.log"})
            runtime = run_command(command, args.work, env, destination / "runtime.log", 60)
            commands[-1]["returncode"] = runtime.returncode
            runtime_output = runtime.stdout.decode("utf-8", errors="replace")
            if runtime.returncode != 0 or runtime.stdout != EXPECTED_SIMULATION:
                failures.append("simulation did not produce the exact expected result")
    files = snapshot_files(args.work, destination / "artifacts")
    for required in case.required:
        if required not in files:
            failures.append("missing required artifact: " + required)
    result = {"commands": commands, "files": files, "failures": failures,
              "runtime_output": runtime_output}
    (destination / "manifest.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def binary_difference(old: bytes, new: bytes) -> dict:
    first = next((i for i, (a, b) in enumerate(zip(old, new)) if a != b),
                 min(len(old), len(new)))
    start, stop = max(0, first - 24), first + 48
    return {"old_bytes": len(old), "structural_bytes": len(new),
            "first_difference": first, "context_offset": start,
            "old_hex": old[start:stop].hex(), "structural_hex": new[start:stop].hex()}


def describe_difference(case: Case, relative: str, args, env: dict) -> dict:
    old = args.results / case.name / "old" / "artifacts" / relative
    new = args.results / case.name / "structural" / "artifacts" / relative
    diag = args.results / case.name / "differences" / relative
    diag.parent.mkdir(parents=True, exist_ok=True)
    details = binary_difference(old.read_bytes(), new.read_bytes())
    (Path(str(diag) + ".bytes.json")).write_text(json.dumps(details, indent=2) + "\n")
    suffix = Path(relative).suffix
    if suffix in {".bo", ".ba"}:
        tool = "dumpbo" if suffix == ".bo" else "dumpba"
        dumps = []
        # Each dumper sees the same original relative path, not a snapshot path.
        for label, bins, artifact in [("old", args.old_bin, old),
                                       ("structural", args.structural_bin, new)]:
            working_artifact = args.work / relative
            working_artifact.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(artifact, working_artifact)
            log = Path(str(diag) + "." + label + ".dump")
            command_env = dict(env)
            command_env["PATH"] = str(bins) + os.pathsep + env.get("PATH", "")
            proc = run_command([str(bins / tool), relative], args.work, command_env, log, args.timeout)
            dumps.append(proc.stdout.decode("utf-8", errors="replace"))
            details[label + "_dump_returncode"] = proc.returncode
        before, after = dumps
    else:
        before = old.read_bytes().decode("utf-8", errors="replace")
        after = new.read_bytes().decode("utf-8", errors="replace")
    diff = "".join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
                                       fromfile="old/" + relative, tofile="structural/" + relative))
    Path(str(diag) + ".diff").write_text(diff)
    details["decoded_text_equal"] = before == after
    return details


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--old-bin", required=True, type=Path)
    parser.add_argument("--structural-bin", required=True, type=Path)
    parser.add_argument("--runtime", required=True, type=Path,
                        help="one shared BLUESPECDIR for both compilers")
    parser.add_argument("--fixtures", type=Path,
                        default=Path(__file__).resolve().parent / "component-parity-fixtures")
    parser.add_argument("--work", type=Path,
                        help="scratch directory; default: retained temporary run directory")
    parser.add_argument("--results", type=Path,
                        help="fresh evidence directory; default: retained temporary run directory")
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    if args.work is None or args.results is None:
        run_root = Path(tempfile.mkdtemp(prefix="bsc-component-parity-"))
        args.work = args.work or run_root / "component-parity-work"
        args.results = args.results or run_root / "results"
    for name in ["old_bin", "structural_bin", "runtime", "fixtures", "work", "results"]:
        setattr(args, name, getattr(args, name).resolve())
    for bins in [args.old_bin, args.structural_bin]:
        for executable in ["bsc", "bluetcl", "dumpbo", "dumpba"]:
            if not (bins / executable).is_file():
                parser.error("missing binary: " + str(bins / executable))
    if not (args.runtime / "Libraries").is_dir():
        parser.error("runtime must contain Libraries")
    for source in {case.source for case in CASES}:
        if not (args.fixtures / source).is_file():
            parser.error("missing fixture: " + str(args.fixtures / source))
    if args.work == args.results or args.work in args.results.parents:
        parser.error("--results must be outside the scratch directory")
    if args.work == args.fixtures or args.work in args.fixtures.parents:
        parser.error("--fixtures must be outside the scratch directory")
    if args.results.exists():
        parser.error("results already exist; pass a fresh --results path to retain previous evidence")
    args.results.mkdir(parents=True)
    env = dict(os.environ)
    env.update({"BLUESPECDIR": str(args.runtime), "BSDIR": str(args.runtime), "LC_ALL": "C"})
    summary = {"old_bin": str(args.old_bin), "structural_bin": str(args.structural_bin),
               "runtime": str(args.runtime), "work": str(args.work), "cases": {},
               "normalization": "none"}
    failed = False
    for case in CASES:
        print("Running " + case.name + " at " + str(args.work), flush=True)
        runs = {label: run_case(case, label, bins, args, env)
                for label, bins in [("old", args.old_bin), ("structural", args.structural_bin)]}
        old_files, new_files = runs["old"]["files"], runs["structural"]["files"]
        missing_old = sorted(set(new_files) - set(old_files))
        missing_new = sorted(set(old_files) - set(new_files))
        differences = {}
        equal = []
        for name in sorted(set(old_files) & set(new_files)):
            if old_files[name] == new_files[name]:
                equal.append(name)
            else:
                differences[name] = describe_difference(case, name, args, env)
        errors = {label: result["failures"] for label, result in runs.items() if result["failures"]}
        status = "PASS" if not (missing_old or missing_new or differences or errors) else "FAIL"
        failed |= status == "FAIL"
        summary["cases"][case.name] = {"status": status, "equal_artifacts": equal,
            "missing_old": missing_old, "missing_structural": missing_new,
            "differences": differences, "errors": errors}
        (args.results / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        print(f"{status} {case.name}: {len(equal)} exact artifacts, {len(differences)} mismatches", flush=True)
    print("Evidence: " + str(args.results), flush=True)
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
