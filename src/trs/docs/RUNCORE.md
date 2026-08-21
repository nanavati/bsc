# RunCore: self-sufficient AOT boot

Goal (init-ladder terminal rung): an artifact run whose boot is
`mmap the .so + fill the arena from a baked image + dlsym three
tables`, skipping the three measured boot masses — snap decode
(3-4ms), `Interp::new` instantiation (5-7ms), and planning (~1.5ms,
CFL warm laps).  The remaining Verilator deficits across the bench
pool (`FloatTest` -2.8, `TrafficBRAM` -3.3, `BRAM0Test` -8.2, `CFL`
-9.1ms at the full-pool stamp) each equal their measured boot mass;
RunCore is the sweep lever.

## Census: what compiled code actually calls back into

Measured on the slim runner (callgrind + code audit):

- `trs_bram_tick_cb` — pure arena, no interp state
- `jit_foreign_cb` — $display family, $finish/$stop, value tasks
- `jit_prim_cb` — boxed-prim bounces (ZERO on Dividers; near-zero
  elsewhere post Counter-arena; guarded FIFO warn-bounces exist)
- `STRING_CONCAT` — interns into the dyn string table
- stdio flush hooks

Whole-run Dividers = 4.2M Ir, of which boot ~3.3M (malloc + sip
hashing + snap decode).

## What the artifact already carries (no sidecar needed)

- **Ordinal-indexed fn tables**: `trs_edge_tab` (fused per-comp edge
  fns), `trs_sched_tab`, `trs_exec_tab`, with `_len` globals.  Three
  dlsyms resolve every function; no symbol-name table needed.
- **Foreign/prim call-site tables**: the `trs_protos` global
  (`encode_protos` wire format) bakes per-ordinal
  `ForeignSpec`/`PrimCallSpec` tables — token `(ordinal, kind,
  local)` resolves without trial_lower.
- **Patchable callback globals**: `trs_cb_foreign`, `trs_cb_prim`,
  `trs_cb_stdio`, BDPI callee globals — the loader writes function
  addresses in; a RunCore boot patches in RunCore-flavored callbacks
  instead of the Interp-backed ones.
- **Compiled ticks**: `trs_edge_wire_ticks` level 2 = wire clears +
  cregs + brams inside the edge fns.

## Sidecar v1 (landed, corpus-proven)

`<base>.arena` = `b"TRSARENA"` + LE u64 header `[version=1,
AOT_LAYOUT_REV, salted bir_hash, nslots]` + RLE `(value, run)`
pairs.  Emitted by the link's Emit arm from the SAME four steps as
the load tail (alloc, attach, reset levels, memo stamps).
`TRS_RUNCORE_CHECK=1` bit-compares on every Path load; dual-built
across all 996 corpus designs with zero mismatches.  Gated out:
traced designs (`vcd_trace` — rec_inits apply later, wave engine
needs the interp) and mem-file designs (arena tracks files that may
change between link and run).

## Sidecar v2 (next): the boot descriptor

Additional sections, all emit-time-known in the Emit-Ok arm:

1. **String table** — the design's full `d.strings` (StrDyn tokens
   may select any id at run time, so the whole table, not just the
   referenced subset).  Dyn interning appends past its length,
   exactly like the interp's `dyn_strs`.
2. **Instance paths** — `insts[i].path` for every inst referenced by
   a `ForeignSpec` (%m locations) and every BRAM warn registration.
3. **Clock config** — the single periodic Wave clock's `hi`, `lo`
   (central-loop eligibility guarantees exactly one, on the default
   clock).
4. **Posedge comp order** — the comp ordinals the central loop calls
   per posedge (`pos_rcis`), in call order; plus the verified claim
   that every negedge comp is skippable (rule-less, covered ticks).
5. **BRAM warn names** — (arena block base offset, full name) pairs
   so `BRAM_WARN` warnings keep name parity without prim structs.
6. **Eligibility flag** — the conjunction the emitter can prove:
   all comps fused, tick level 2 with no uncovered non-reset ticks,
   no early rules, single default Wave clock, no reset generators,
   no dynamic/driver clocks, no $dump* strings in the design, no
   BDPI imports (rung 1; BDPI later via the existing callee
   globals).  No flag → classic boot, silently.

Validation discipline (same as v1): the classic boot path under
`TRS_RUNCORE_CHECK=1` recomputes each section from the live plan and
bit-compares against the sidecar — corpus-prove v2 before the driver
trusts a byte of it.

## The driver (after v2)

A `RunCore` context (NOT an `Interp`): the `ForeignEnv` split
(foreign.rs) owns console/file/finish/plusargs/timescale state and
services the design-independent arms wholesale; `envp` points at the
RunCore context and `runcore_foreign_cb` mirrors `jit_foreign_cb`
over baked tables (protos from the .so, strings/paths from v2).

Run shape = the central loop's steady state (fused edge fns over
`pos_rcis`, tp/tn bookkeeping, finished/stop checks) plus the early
instants the general loop handles today:

- t=0: top reset asserted (kernel-driven), initial edges fire with
  reset conds holding rules off (reset wire slots in the arena carry
  the asserted level; the baked image holds boot-time levels).
- t=2: deassert after that instant's logic, then steady loop.

The exact assert/deassert choreography must byte-match the general
loop (witnesses: any design that $displays during the reset window).
This is the driver's correctness core — replicate, then diffsweep.

## Lazy Reflect (after the driver)

The `ForeignEnv` decline set is the materialization trigger list:
`$dump*` arms and `jit_prim_cb` bounces build the full Interp
mid-run.  First-bounce invariant: no boxed history exists at
materialization, so fresh prims + attach-WITHOUT-clobber is exact —
today's `arena_attach` writes struct state into slots, so an attach
mode that adopts slot state instead is prerequisite work.

## Follow-ups queued behind the driver

- Post-reset arena image: skip the reset window too, gated on an
  output-silent reset window (checkable during dual-build).
- BDPI-importing designs (callee globals already exist).
- Relink-on-demand for batch -V on RunCore-booted artifacts.

## Registered predictions (to score when the driver lands)

Dividers ~1.8-2.2ms, CFL ~5-8ms, TrafficBRAM at-or-under Verilator,
8-9/10 bench-pool designs boot RunCore (mem-file + traced classic).

## The driver's parity contract (rung 3a, landed)

Confirmed by the adversarial panel as the items the boot must state,
not assume:

- **Exit code**: 1 iff `$fatal` fired; `$finish(n)`'s status NEVER
  surfaces as the process exit code; `$stop` is a yield and the batch
  run then exits 0.  (`runcore::try_boot` returns exactly
  `fataled as i32`; witnessed by the regress battery under
  `TRS_RUNCORE=1` — FinishEdge et al. compare exit codes.)
- **Routing**: any selfcheck (flag or `TRS_SELFCHECK`), any wave
  request (`-V`, `+bscvcd`/`+bscfst`, link formats), `TRS_JIT`, and
  the interactive/exe tiers all boot classic; the slim binary's
  dispatch execs the full binary for selfcheck/jit before run_file is
  ever reached.
- **Eligibility semantics revision**: the sidecar VERSION is the
  eligibility-semantics revision.  Any change to the gate rules bumps
  it (2 = pre-prim-gate, refused as stale; 3 = current), so a newer
  driver never trusts an `eligible` flag computed under older rules.
- **Known witness blind spots (minor, ledgered)**: the inverse
  eligibility witness triggers only on `$finish`-terminated runs
  (cycle-limit and event-exhaustion endings are unwitnessed), and
  `central_engaged` is monotone per Interp — refine when the witness
  next changes shape.
