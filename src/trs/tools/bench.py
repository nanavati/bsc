#!/usr/bin/env python3
"""Three-simulator benchmark: Bluesim vs Verilator vs trs.

Two axes per design:
  build   bsc frontend (elab) + backend-specific build:
            bluesim  = bsc -sim -e (C++ codegen + g++)
            verilator= bsc -verilog -u -g + verilator --cc + make
            trs      = bsc -sim -bir -e (.bir export) + trs link
  run     wall time to natural $finish (median of --runs), peak RSS.
          cycles/s where the design's cycle count is known.

Fairness ground rules (docs/BENCH.md):
  - every leg runs SINGLE-THREADED;
  - Verilator runs WITHOUT --timing (known issues; per Ravi) — a
    generic C++ clock driver toggles CLK/RST_N on the bsc top instead
    of the reference main.v, so all three legs simulate the same
    closed testbench module;
  - designs terminate themselves ($finish): no -m games, identical
    workload per leg;
  - numbers from an uncalibrated/shared box are INDICATIVE — the
    authoritative fence runs on the calibrated machine.

Usage:
  bench.py [--filter substr] [--runs 3] [--legs bluesim,verilator,trs]
           [--out bench-results.json]
  env: BSC, TRS, BENCH_WORK (workdir; default: fresh temp)
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
BSC = os.environ.get("BSC", "bsc")
TRS = os.environ.get("TRS", "trs")

# The pool: closed ($finish-terminating) testbenches chosen from sweep
# telemetry for per-cycle weight, covering distinct simulator stress
# characters.  `cycles` is the design's own workload when known (for
# cycles/s); None = report wall time only.
POOL = [
    # pure edge throughput: one rule, one counter, 300M posedges
    dict(name="Long", dir="testsuite/bsc.bluesim/interactive",
         src="Long.bsv", top="mkLong", cycles=300_000_001,
         character="raw edge/rule dispatch floor"),
    # scheduling weight: very large rule count with conflict analysis
    dict(name="ConflictFreeLarge", dir="testsuite/bsc.long_tests/conflict_free_large",
         src="ConflictFreeOKLarge.bsv", top="sysConflictFreeOKLarge", cycles=None,
         character="huge rule count per cycle (scheduler-bound)"),
    # FP pipeline dataflow (PAClib DFT, 64-pt): FIFOs + FP mul/add
    dict(name="DFT64v1", dir="testsuite/bsc.lib/PAClib/dft64/bsv",
         src="Tb.bsv", top="sysTb_v1", cycles=None,
         character="FP dataflow pipeline, FIFO-heavy"),
    dict(name="DFT64v5", dir="testsuite/bsc.lib/PAClib/dft64/bsv",
         src="Tb.bsv", top="sysTb_v5", cycles=None,
         character="FP dataflow, deeper variant"),
    # FP arithmetic battery (add/mul/div/sqrt corner cases)
    dict(name="FloatTest", dir="testsuite/bsc.lib/FloatingPoint",
         src="FloatTest.bsv", top="sysFloatTest", cycles=None,
         character="FP arithmetic battery, wide values"),
    # BRAM traffic through a MIMO buffer
    dict(name="TrafficBRAM", dir="testsuite/bsc.bsv_examples/mimo",
         src="TrafficBRAM.bsv", top="sysTrafficBRAM", cycles=None,
         character="BRAM + MIMO buffering, memory-port bound"),
    # BRAM byte-enable/init battery
    dict(name="BRAM0Test", dir="testsuite/bsc.lib/BRAM/BRAM0Test",
         src="BRAM0Test.bsv", top="sysBRAM0Test", cycles=None,
         character="BRAM variants battery, wide state"),
    # combinational search (sudoku generator)
    dict(name="Sudoku", dir="testsuite/bsc.bsv_examples/sudoku",
         src="GenerateTest.bsv", top="mkGenerateTest3", cycles=None,
         character="deep combinational cones, backtracking search"),
    # iterative arithmetic (Randomize-fed dividers)
    dict(name="Dividers", dir="testsuite/bsc.lib/Divide",
         src="Test_mkNonPipelinedDivider.bsv", top="sysTest_mkNonPipelinedDivider",
         cycles=None, character="iterative arithmetic + $random operands",
         random=True),
    # sparse RegFile addressing
    dict(name="SparseRF", dir="testsuite/bsc.bluesim/misc",
         src="SparseRF.bsv", top="sysSparseRF", cycles=None,
         character="RegFile range traffic"),
    # packet-processing app (mesa)
    dict(name="Mesa", dir="testsuite/bsc.bsv_examples/mesa",
         src="mkTestMesa.bsv", top="sysTestMesa", cycles=None,
         character="app-scale packet pipeline"),
]

VL_MAIN = r"""
// generic Verilator driver for a closed bsc top (CLK/RST_N only) —
// replaces main.v so no --timing is needed
#include "V%TOP%.h"
#include "verilated.h"
int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    V%TOP%* top = new V%TOP%;
    vluint64_t half = 0;
    top->RST_N = 0;
    top->CLK = 0;
    top->eval();
    while (!Verilated::gotFinish()) {
        ++half;
        if (half == 4) top->RST_N = 1;   // 2 full cycles of reset
        top->CLK = !top->CLK;
        top->eval();
        if (half > 8000000000ULL) break; // 4G-cycle safety cap
    }
    top->final();
    delete top;
    return 0;
}
"""


# Benchmark hygiene: a stray TRS_SELFCHECK=1 in the caller's shell
# (say, right after a suite run) would silently run lockstep shadows
# inside the trs leg and triple its numbers.  The selfcheck is a
# validation mode, never a benchmark mode — scrub its knobs (and the
# jit trace) from every child environment.
_ENV = {k: v for k, v in os.environ.items()
        if not k.startswith("TRS_SELFCHECK") and k != "TRS_JIT_TRACE"}


def sh(cmd, cwd, env=None, timeout=7200):
    t0 = time.monotonic()
    r = subprocess.run(cmd, cwd=cwd, env=env or _ENV,
                       capture_output=True, text=True, timeout=timeout)
    return r, time.monotonic() - t0


def run_measured(cmd, cwd, runs):
    """Median wall + max RSS over `runs` executions.

    RSS comes from /usr/bin/time %M per run, NOT from
    getrusage(RUSAGE_CHILDREN): ru_maxrss there is a cumulative
    high-water mark over every child ever waited on, so one big build
    child (bsc peaks ~300MB) masquerades as every later run's RSS.
    """
    walls, rss = [], 0
    out = None
    for _ in range(runs):
        with tempfile.NamedTemporaryFile(mode="r", suffix=".rss") as tf:
            r, w = sh(["/usr/bin/time", "-f", "%M", "-o", tf.name] + cmd, cwd)
            if r.returncode not in (0,):
                return None, r
            try:
                rss = max(rss, int(tf.read().strip().splitlines()[-1]))
            except (ValueError, IndexError):
                pass
        walls.append(w)
        out = r
    walls.sort()
    return dict(wall=walls[len(walls) // 2], walls=walls,
                max_rss_kb=rss), out


def bench_one(d, legs, runs, work):
    res = dict(name=d["name"], top=d["top"], character=d["character"], legs={})
    src_dir = os.path.join(REPO, d["dir"])
    top = d["top"]
    outputs = {}
    for leg in legs:
        wk = os.path.join(work, d["name"], leg)
        os.makedirs(wk, exist_ok=True)
        for f in os.listdir(src_dir):
            if f.endswith((".bsv", ".bs", ".c", ".h", ".hex", ".bin", ".dat", ".txt", ".vec")):
                try:
                    shutil.copy(os.path.join(src_dir, f), wk)
                except OSError:
                    pass
        common = ["-bdir", wk, "-info-dir", wk, "-simdir", wk, "-vdir", wk,
                  "-p", wk + ":+"]
        L = {}
        if leg in ("bluesim", "trs"):
            r, t = sh([BSC, "-sim", "-u", "-g", top] + common + [d["src"]], wk)
            if r.returncode != 0:
                L["error"] = "bsc compile: " + (r.stderr or r.stdout)[-300:]
                res["legs"][leg] = L
                continue
            L["frontend_s"] = round(t, 2)
            if leg == "bluesim":
                r, t = sh([BSC, "-sim", "-e", top, "-o", "simb"] + common, wk)
                if r.returncode != 0:
                    L["error"] = "bluesim link: " + (r.stderr or r.stdout)[-300:]
                    res["legs"][leg] = L
                    continue
                L["backend_s"] = round(t, 2)
                m, r = run_measured(["./simb"], wk, runs)
                exe = "./simb"
            else:
                r, t = sh([BSC, "-sim", "-bir", "-e", top, "-o", "simr"] + common, wk)
                bir = os.path.join(wk, top + ".bir")
                if not os.path.exists(bir):
                    L["error"] = "no .bir: " + (r.stderr or r.stdout)[-300:]
                    res["legs"][leg] = L
                    continue
                r2, t2 = sh([TRS, "link", bir, "-o", "art"], wk)
                if r2.returncode != 0:
                    L["error"] = "trs link: " + (r2.stderr or r2.stdout)[-300:]
                    res["legs"][leg] = L
                    continue
                L["backend_s"] = round(t2, 2)
                L["bir_export_s"] = round(t, 2)
                m, r = run_measured(["./art"], wk, runs)
                exe = "./art"
        else:  # verilator
            r, t = sh([BSC, "-verilog", "-u", "-g", top] + common + [d["src"]], wk)
            if r.returncode != 0:
                L["error"] = "bsc -verilog: " + (r.stderr or r.stdout)[-300:]
                res["legs"][leg] = L
                continue
            L["frontend_s"] = round(t, 2)
            # bsc >= this tree emits the system-task blocks' 0-tick
            # ordering guard as `BSV_TASKS_DELAY (defined away below);
            # the strip stays as a fallback for benchmarking OLDER bsc
            # revisions, whose literal `#0;` predates the macro.  It is
            # inert under the C++ driver either way (the negedge
            # instant is a plain eval long after posedge NBAs settle).
            for vf in os.listdir(wk):
                if vf.endswith(".v"):
                    pv = os.path.join(wk, vf)
                    txt = open(pv).read()
                    txt2 = re.sub(r"^\s*#0;\s*$", "", txt, flags=re.M)
                    if txt2 != txt:
                        open(pv, "w").write(txt2)
            with open(os.path.join(wk, "bench_main.cpp"), "w") as f:
                f.write(VL_MAIN.replace("%TOP%", top))
            vdir = os.path.join(os.path.dirname(shutil.which(BSC) or BSC),
                                "..", "lib", "Verilog")
            # no timing flags at all (per Ravi: --timing has known
            # issues, and --no-timing would silently ignore stray
            # delays): the assignment delay is `define'd away instead,
            # so the Verilog is genuinely delay-free and anything else
            # timing-shaped errors loudly for explicit handling
            r, t = sh(["verilator", "--cc", "--exe", "--build", "-j", "4",
                       "+define+BSV_ASSIGNMENT_DELAY=",
                       "+define+BSV_TASKS_DELAY=",
                       "+define+BSV_ZERO_DELAY=",  # transitional name, harmless if unused
                       # every leg's generated C++ builds -O3: Bluesim
                       # ships c++ -O3, but Verilator's packaged
                       # verilated.mk defaults OPT_FAST/OPT_GLOBAL to
                       # -Os — a size-optimized eval loop measured 34%
                       # slower on the dispatch floor (mkLong)
                       "-MAKEFLAGS", "OPT_FAST=-O3",
                       "-MAKEFLAGS", "OPT_GLOBAL=-O3",
                       "-O3", "-Wno-fatal",
                       "--x-assign", "fast", "--x-initial", "fast",
                       "-y", os.path.abspath(vdir),
                       top + ".v", "bench_main.cpp", "-o", "simv"], wk)
            if r.returncode != 0:
                L["error"] = "verilator: " + (r.stderr or r.stdout)[-300:]
                res["legs"][leg] = L
                continue
            L["backend_s"] = round(t, 2)
            m, r = run_measured(["./obj_dir/simv"], wk, runs)
            exe = "./obj_dir/simv"
        if m is None:
            L["error"] = f"run {exe}: rc={r.returncode} " + (r.stderr or "")[-200:]
        else:
            L["run_s"] = round(m["wall"], 3)
            L["runs_s"] = [round(x, 3) for x in m["walls"]]
            L["max_rss_kb"] = m["max_rss_kb"]
            if d.get("cycles"):
                L["mcycles_per_s"] = round(d["cycles"] / m["wall"] / 1e6, 2)
            outputs[leg] = (r.stdout or "").strip()
        res["legs"][leg] = L
    # cross-leg output check: same testbench must print the same thing.
    # Verilator appends its own "$finish" trailer — normalize it away;
    # $random designs are exempt on the verilator leg (Verilator's RNG
    # is not glibc's, so the operand stream legitimately differs).
    def norm(t):
        return "\n".join(
            l for l in t.strip().splitlines()
            if not re.match(r"^- .*Verilog \$finish", l)
        ).strip()
    outs = {k: norm(v) for k, v in outputs.items()}
    if d.get("random"):
        outs.pop("verilator", None)
    if len(set(outs.values())) > 1:
        res["output_mismatch"] = {k: v[-200:] for k, v in outs.items()}
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--filter", default="")
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--legs", default="bluesim,verilator,trs")
    ap.add_argument("--out", default="bench-results.json")
    args = ap.parse_args()
    legs = [l for l in args.legs.split(",") if l]
    work = os.environ.get("BENCH_WORK") or os.path.join(
        os.environ.get("TMPDIR", "/tmp"), f"trs-bench-{os.getpid()}")
    os.makedirs(work, exist_ok=True)
    results = []
    for d in POOL:
        if args.filter and args.filter not in d["name"]:
            continue
        print(f"== {d['name']} ({d['character']})", flush=True)
        res = bench_one(d, legs, args.runs, work)
        results.append(res)
        for leg, L in res["legs"].items():
            if "error" in L:
                print(f"   {leg:9} ERROR {L['error'][:120]}")
            else:
                extra = f" {L['mcycles_per_s']} Mc/s" if "mcycles_per_s" in L else ""
                print(f"   {leg:9} build {L.get('frontend_s', 0):7.2f}+"
                      f"{L.get('backend_s', 0):7.2f}s  run {L.get('run_s', 0):8.3f}s"
                      f"  rss {L.get('max_rss_kb', 0) // 1024}MB{extra}")
        if "output_mismatch" in res:
            print("   !! OUTPUT MISMATCH across legs")
    with open(args.out, "w") as f:
        json.dump(results, f, indent=1)
    print(f"results: {args.out}  (workdir kept: {work})")


if __name__ == "__main__":
    main()
