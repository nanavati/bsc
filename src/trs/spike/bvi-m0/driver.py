#!/usr/bin/env python3
"""M0 spike driver: contract fixture -> verilate -> shim -> ctypes harness.

Implements the v4 shadow-vector protocol in Python against the shim ABI
and runs fixture scenarios.  Usage:
    driver.py <verilator-binary> <fixture-name> [workdir]
Exit 0 on scenario pass; nonzero with a specific message otherwise.
"""
import ctypes
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).parent
sys.path.insert(0, str(HERE))
import metaparse  # noqa: E402
import shimgen    # noqa: E402


def build(vlt, contract, workdir):
    top = contract["verilog_name"]
    work = Path(workdir); work.mkdir(parents=True, exist_ok=True)
    rtl = HERE / "rtl" / f"{top}.v"

    meta = metaparse.extract(vlt, top, [rtl], workdir=work / "meta")
    (work / "meta.json").write_text(json.dumps(meta, indent=2))

    if meta["has_delay"]:
        raise SystemExit(f"REFUSE(delay): {top} contains delays")
    if meta["has_dpi"]:
        raise SystemExit(f"REFUSE(dpi): {top} contains DPI")

    chash = shimgen.gen(contract, meta, work / "shim.cpp")

    obj = work / "obj"
    decl = HERE / "trs_printf_decl.h"
    defines = f"-DVL_USER_FATAL -DVL_PRINTF=trs_vlt_printf -include {decl} -fPIC"
    r = subprocess.run(
        [vlt, "--cc", "--no-timing", "--x-assign", "0", "--x-initial", "0",
         "-O2", "--assert", "--top-module", top, "-Mdir", str(obj),
         "-CFLAGS", defines, str(rtl)],
        capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"verilate failed:\n{r.stderr}")
    r = subprocess.run(
        ["make", "-s", "-C", str(obj), "-f", f"V{top}.mk",
         f"V{top}__ALL.a", "verilated.o", "verilated_threads.o"],
        capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"model build failed:\n{r.stderr}\n{r.stdout}")

    vroot = subprocess.run([vlt, "--getenv", "VERILATOR_ROOT"],
                           capture_output=True, text=True).stdout.strip()
    so = work / f"lib{top}_shim.so"
    r = subprocess.run(
        ["g++", "-shared", "-fPIC", "-O2", "-std=c++17",
         "-DVL_USER_FATAL", "-DVL_PRINTF=trs_vlt_printf", "-include", str(HERE / "trs_printf_decl.h"),
         "-I", str(obj), "-I", f"{vroot}/include", "-I", f"{vroot}/include/vltstd",
         str(work / "shim.cpp"),
         str(obj / f"V{top}__ALL.a"),
         str(obj / "verilated.o"), str(obj / "verilated_threads.o"),
         "-lpthread", "-lz", "-o", str(so)],
        capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"shim link failed:\n{r.stderr}")
    return so, chash


class Bvi:
    """Shadow-vector protocol over the shim ABI (v4 sec 4.1)."""

    def __init__(self, so_path, contract):
        self.lib = ctypes.CDLL(str(so_path))
        self.lib.vlt_new.restype = ctypes.c_void_p
        self.lib.vlt_new.argtypes = [ctypes.c_char_p, ctypes.c_int,
                                     ctypes.POINTER(ctypes.c_char_p)]
        self.lib.vlt_contract.restype = ctypes.c_char_p
        self.lib.vlt_fatal_msg.restype = ctypes.c_char_p
        self.contract = contract
        self.pidx = {p["name"]: i for i, p in enumerate(contract["ports"])}
        self.h = ctypes.c_void_p(self.lib.vlt_new(b"m0", 0, None))
        assert self.h.value, "vlt_new failed"
        self.shadow = {}       # port name -> value (pending publication)
        self.published = {}    # last published values
        self.dirty = True      # born true (initial blocks must run)
        self.pending_edges = {}  # port name -> level
        self.en_group = []     # ENs to clear post-edge
        self.time = 0

    def _limbs(self, width, value):
        n = max(1, (width + 63) // 64)
        arr = (ctypes.c_uint64 * n)()
        for i in range(n):
            arr[i] = (value >> (64 * i)) & 0xFFFFFFFFFFFFFFFF
        return arr

    def _set(self, name, value):
        p = self.contract["ports"][self.pidx[name]]
        rc = self.lib.vlt_set(self.h, self.pidx[name],
                              self._limbs(p["width"], value))
        assert rc == 0, f"vlt_set({name}) rc={rc}: {self.lib.vlt_fatal_msg().decode()}"

    def _get(self, name):
        p = self.contract["ports"][self.pidx[name]]
        n = max(1, (p["width"] + 63) // 64)
        arr = (ctypes.c_uint64 * n)()
        rc = self.lib.vlt_get(self.h, self.pidx[name], arr)
        assert rc == 0, f"vlt_get({name}) rc={rc}"
        v = 0
        for i in range(n):
            v |= arr[i] << (64 * i)
        return v

    def drive(self, name, value):
        """Shadow update -- no eval."""
        if self.published.get(name) != value:
            self.shadow[name] = value

    def _publish_and_settle(self):
        for k, v in self.shadow.items():
            self._set(k, v)
            self.published[k] = v
            self.dirty = True
        self.shadow.clear()
        if self.dirty:
            self.lib.vlt_set_time(self.h, self.time)
            rc = self.lib.vlt_eval(self.h)
            assert rc == 0, f"eval failed: {self.lib.vlt_fatal_msg().decode()}"
            self.dirty = False

    # -- protocol operations -------------------------------------------
    def call_action(self, method, **args):
        m = self._method(method)
        for aname, aval in args.items():
            self.drive(aname, aval)
        if m["enable"]:
            self.drive(m["enable"], 1)
            self.en_group.append(m["enable"])

    def observe(self, port):
        """Observation frontier: publish everything dirty, settle, read."""
        self._publish_and_settle()
        return self._get(port)

    def commit_edge(self, clock_ports_high, dt=5):
        """Three-phase batched commit (v4 4.1 step 4)."""
        self.time += dt
        # (a) inputs
        self._publish_and_settle()
        # (b) edges -- all coincident clock levels, one eval
        for cp, lvl in clock_ports_high.items():
            self._set(cp, lvl)
            self.published[cp] = lvl
        self.lib.vlt_set_time(self.h, self.time)
        rc = self.lib.vlt_eval(self.h)
        assert rc == 0, f"edge eval failed: {self.lib.vlt_fatal_msg().decode()}"
        # (c) post -- clear ENs, settle
        for en in self.en_group:
            self._set(en, 0)
            self.published[en] = 0
        self.en_group.clear()
        rc = self.lib.vlt_eval(self.h)
        assert rc == 0
        self.dirty = False

    def set_reset(self, port, level):
        self.drive(port, level)
        self._publish_and_settle()

    def _method(self, name):
        for m in self.contract["methods"]:
            if m["name"] == name:
                return m
        raise KeyError(name)

    def close(self):
        self.lib.vlt_free(self.h)


def scenario_counter(so, contract):
    b = Bvi(so, contract)
    # startup: deassert-init, settle (initial blocks run), then t=0 assert
    b.drive("CLK", 0)
    b.drive("RST_N", 1)
    _ = b.observe("count")            # forces initial publish+settle
    b.set_reset("RST_N", 0)           # real assertion transition
    b.commit_edge({"CLK": 1}); b.commit_edge({"CLK": 0})
    b.set_reset("RST_N", 1)           # deassert
    got = []
    for cyc in range(4):
        rdy = b.observe("RDY_bump")
        assert rdy == 1, f"RDY low at cycle {cyc}"
        b.call_action("bump", bump_amt=3)
        pre = b.observe("count")      # value read BEFORE edge: old value
        b.commit_edge({"CLK": 1})
        post = b.observe("count")     # after edge: committed
        b.commit_edge({"CLK": 0})
        got.append((pre, post))
    expect = [(0, 3), (3, 6), (6, 9), (9, 12)]
    assert got == expect, f"counter mismatch: {got} vs {expect}"
    b.close()
    return "counter: pre/post per cycle == hand-derived NBA semantics"


SCENARIOS = {"counter": scenario_counter}


def main():
    vlt, fixture = sys.argv[1], sys.argv[2]
    workdir = sys.argv[3] if len(sys.argv) > 3 else str(HERE / "out" / fixture)
    contract = json.loads((HERE / "contracts" / f"{fixture}.json").read_text())
    so, chash = build(vlt, contract, workdir)
    msg = SCENARIOS[fixture](so, contract)
    print(f"PASS [{fixture}] contract={chash} :: {msg}")


if __name__ == "__main__":
    main()
