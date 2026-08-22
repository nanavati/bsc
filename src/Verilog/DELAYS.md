# Delay (`#`) idioms in the Verilog primitive library

This is an audit of every delay statement in the primitive library,
classifying each and recording why it is kept.  Context: the
`-vsim verilator` flow builds these files with Verilator, which since
version 5 requires choosing `--no-timing` (delays ignored; the
historical mode, with STMTDLY/INITIALDLY lint waived in
`verilator_config.vlt`) or `--timing` (delays honored, using
`verilator_config_timing.vlt`).  On this branch the choice is
automatic: bsc analyzes the design's `.ba` hierarchy at link time and
builds designs that generate a clock or reset (or link without main.v)
with `--timing`; everything else stays `--no-timing`.  Overrides:
`BSC_VERILATOR_TIMING=1`/`-Xv --timing` forces timing on,
`BSC_VERILATOR_TIMING=0`/`-Xv --no-timing` forces it off (refusing
needs-timing designs with a clear message).  Event-driven simulators (iverilog,
VCS, ...) always honor these delays, so removing or changing any of
them changes behavior under those simulators; every delay below is
therefore kept.

## Classification

1. **init-#0** — `initial begin #0; <register initialization> end`
   (inside `BSV_NO_INITIAL_BLOCKS`/`translate_off` guards).  The `#0`
   postpones the initialization to the end of the time-0 slot, after
   every `always` block has started waiting, so the X-to-initial-value
   transition is *seen* as an event (InitialReset.v documents the
   canonical reason: "Required so that negedge is seen by any derived
   async resets").  Redundant under Verilator `--no-timing` (delays
   ignored, statically initialized), honored and harmless under
   `--timing`, load-bearing under event-driven simulators.  Kept.

2. **assert-#0** — `#0` at the end of a parameter-assertion `initial`
   block, immediately before `if (ok == 0) $finish`: lets every
   assertion block in the design print its message before the first
   `$finish` takes effect.  Kept.

3. **comb race-dodge** — a delay at the top of a combinational
   `always` block that recomputes `PREEDGE`, delaying the update past
   the clock edge that triggered it (see the Cummings SNUG2002 note
   cited in ClockDiv.v).  Ignored under `--no-timing`, honored under
   `--timing` and event simulators.  Kept.  Note the inconsistency:
   ClockDiv.v uses `#0` where GatedClockDiv.v uses `#1`; both predate
   this audit and both work, so neither is changed.

4. **time source** — delays that *generate* waveforms.  ClockGen.v is
   a clock oscillator implemented entirely by delay (`# initDelay`,
   `# v1Width`, `# v2Width` in a `forever` loop); it is the primitive
   behind `mkAbsoluteClock`.  Under `--no-timing` a design containing
   ClockGen does not even build (Verilator reports INFINITELOOP), so
   such designs require `--timing`.  McpRegUN.v uses a parameterized
   net delay (`#delay`, default 0) to X-poison values that changed
   within a multicycle window; with the delay ignored the check
   degrades to a no-op (never poisons), which is the historical
   `--no-timing` behavior.  Kept.

5. **self-test** — delays inside `` `ifdef testBluespec `` testbench
   modules at the bottom of some files.  `testBluespec` is not defined
   by any build or link flow (checked: no reference outside these
   files), so these are never compiled in normal use.  Kept.

## Table

| File | Line | Delay | Class | Action |
|---|---|---|---|---|
| ClockDiv.v | 62 | `#0` | comb race-dodge | keep |
| ClockDiv.v | 94 | `#0` | init-#0 | keep |
| ClockGen.v | 26 | `#0` | init-#0 (head of clock loop) | keep |
| ClockGen.v | 28,32,34 | `# initDelay`, `# v1Width`, `# v2Width` | time source | keep; requires `--timing` under Verilator |
| ClockGen.v | 77 | `#10000` | self-test | keep (not compiled) |
| ClockMux.v | 53 | `#0` | init-#0 | keep |
| ClockSelect.v | 112 | `#0` | init-#0 | keep |
| GatedClock.v | 85 | `#0` | init-#0 | keep |
| GatedClockDiv.v | 72 | `#1` | comb race-dodge | keep (note: ClockDiv uses `#0` here) |
| GatedClockDiv.v | 110 | `#0` | init-#0 | keep |
| GatedClockInverter.v | 38 | `#0` | init-#0 | keep |
| InitialReset.v | 45 | `#0` | init-#0 | keep (comment in file) |
| MakeClock.v | 113 | `#0` | init-#0 | keep |
| MakeReset.v | 63 | `#0` | init-#0 | keep |
| MakeReset0.v | 58 | `#0` | init-#0 | keep |
| MakeResetA.v | 63 | `#0` | init-#0 | keep |
| McpRegUN.v | 31 | `#delay` (net delay, param, default 0) | time source | keep; inert under `--no-timing` |
| ResetMux.v | 43 | `#0` | init-#0 | keep |
| SyncFIFO.v | 267 | `#0` | assert-#0 | keep |
| SyncFIFO.v | 342,346,350 | `#200`, `#100000`, `#50000` | self-test | keep (not compiled) |
| SyncFIFO0.v | 229 | `#0` | assert-#0 | keep |
| SyncFIFO0.v | 299,303,307 | `#200`, `#100000`, `#50000` | self-test | keep (not compiled) |
| SyncFIFOLevel.v | 378 | `#0` | assert-#0 | keep |
| SyncFIFOLevel.v | 443,445,449 | `#1`, `#200`, `#50000` | self-test | keep (not compiled) |
| SyncFIFOLevel0.v | 340 | `#0` | assert-#0 | keep |
| SyncFIFOLevel0.v | 401,403,407 | `#1`, `#200`, `#50000` | self-test | keep (not compiled) |
| SyncRegister.v | 127 | `#100000` | self-test | keep (not compiled) |
| SyncReset.v | 51 | `#0` | init-#0 | keep |
| SyncResetA.v | 54 | `#0` | init-#0 | keep |
| UngatedClockMux.v | 45 | `#0` | init-#0 | keep |
| UngatedClockSelect.v | 104 | `#0` | init-#0 | keep |

(main.v also uses delays — it is the event-driven simulators'
top-level clock/reset driver and is deliberately excluded from the
Verilator build, where `sim_main.cpp` provides the same schedule.)

## Verilator version note

Three Verilator defects were found while validating `--timing`, each
with a minimal reproducer (kept out of the repo; see the branch notes):

1. **Coroutine crash on double `#0`** — a process that suspends twice
   in one activation with an intervening conditional, e.g.
   `begin #0; ...; if (c) begin ...; #0; end ... end`, which is
   exactly the shape of the `always@(negedge CLK)` system-task blocks
   in BSC-generated Verilog, SIGSEGVs at runtime.  Broken in 5.020
   (Debian/apt, 2024-01) — making 5.020's `--timing` unusable for BSC
   output — and fixed by the 5.050 release.

2. **`$signed(sig[msb:0])` display argument mis-evaluation** —
   `$display("%0d", $signed(v[7:0]))` prints the unsliced value in
   some design shapes.  Correct in 5.020; regressed by 5.050 and
   still present in 5.051-devel.  Hits one testsuite check
   (bsc.verilog/tasks sysModuleDisplay, timing build only).

3. **`--trace --timing` loses `#0`-initial writes** — with tracing
   compiled in (even when not enabled at run time), a register written
   by an `initial begin #0; r = ...; end` block reads back as its
   pre-initialization value in clocked logic.  A 12-line reproducer
   exists.  Correct in 5.020; regressed by 5.050 and still present in
   5.051-devel.  This silently defeats the primitive library's
   init-#0 idiom wherever the initialization value differs from zero —
   visible in the testsuite only under `BSV_POSITIVE_RESET`
   (InitialReset), because elsewhere the init values coincide with
   Verilator's zero-initialization or are immediately overwritten by
   reset.

Net guidance: use Verilator >= 5.050 for `--timing` (5.020 crashes on
any BSC-generated design with system tasks); expect the post-5.020
regressions until they are fixed upstream — a 5.020-vs-5.051 sweep
attributes ~14 checks to them, in BOTH modes (see the failure ledger
below), spanning defect (2), defect (3), a new runtime
`parallel_case` assertion (a behavior change, not a bug — it fires on
BSC's pragma when rules are not actually exclusive), and an abnormal
exit in `$dumpoff`/`$dumpon` handling.

## Validation summary

Slice-level (seven directories, 826 checks — bsc.mcd/{ClockDividers,
MakeClock, Synchronizers, SyncReset, LevelFifo, ClockMux},
bsc.verilog/tasks): iverilog reference 825/0; the new harness under
`--no-timing` is per-test identical to the shipped flow on both
Verilator 5.020 and 5.051.

Full testsuite (`make checkparallel`, 862 test files, ~20,400 checks,
Verilator 5.051-devel, every simulator/compiler invocation under a
timeout and a file-size ulimit):

| run | pass | fail | xfail |
|---|---|---|---|
| verilator `--no-timing` | 19,451 | 800 | 129 |
| verilator `--timing` | 19,851 | 400 | 129 |

Per-test attribution: `--timing` fixes 414 checks (generated clocks,
divided-clock/derived-reset designs that previously failed to build or
hung un-reset) and newly fails 14: 11 are the reset-assertion-edge
startup difference (gated-clock domains can pass one extra clock edge
at time 0 because latches capture out-of-reset state where an event
simulator holds X; runtime opt-out: `BSC_VLT_NO_RESET_EDGE`), and 3
are Verilator defect (3) above.  The 386 failures common to both
modes are pre-existing flow gaps, dominated by Inout-port designs
(~88), foreign-function/BDPI links (~101), and custom-testbench links
in bsc.names/portRenaming (~50), plus known environmental failures
(chmod tests run as root).  `--timing` additionally fixes
sysErrorTest's `$error` exit-status behavior and eliminates every
hang: under `--no-timing`, several divided-clock tests run forever
until killed (one formerly filled the disk with an unbounded VCD).

## Validation summary (automatic mode, verilator-ci base)

Full testsuite with the per-design automatic decision (no environment
overrides: needs-timing designs build `--timing`, everything else
`--no-timing`), on the `verilator-ci` line — which additionally
carries the simulator-derived `use_dpi` testsuite support, module-scope
DPI-C imports, and XFAIL screens for genuine simulator differences:

| run | pass | fail | xfail |
|---|---|---|---|
| verilator, automatic | 18,739 | 79 | 237 |

(The total check count differs from the table above because the
`verilator-ci` testsuite base reworks or removes some test
directories; the comparison below is per-test, not by totals.)

Every one of the 79 failures already fails identically in the forced
`--timing` run on the same code, and none of that run's passes
regressed: the automatic decision reproduces `--timing` behavior
exactly where timing is needed and `--no-timing` behavior elsewhere.
The 79 group as: ~60 golden diffs in the multiple-clock-domain
directories (startup X-artifact display lines, the 11
reset-assertion-edge diffs, same-timestamp ordering); 6 checks hit by
the post-5.020 Verilator `$signed`-slice regression (defect (2)); 3
`parallel_case` runtime assertions in bsc.scheduler/mutually_exclusive;
6 custom-testbench links in bsc.bsv_examples/MacTestBench; and 4
pre-existing environmental/golden failures independent of the
simulator (chmod-as-root tests, DupInclude).  The foreign-function/BDPI
bucket (~101 in earlier runs) is fixed by the DPI support on this
base, and 1 XPASS (sysSmall5 in bsc.names/portRenaming/misc) marks an
XFAIL screen that is now too broad.

## Validation summary (testsuite slices, 2026-08)

Seven slices (bsc.mcd/{ClockDividers, MakeClock, Synchronizers,
SyncReset, LevelFifo, ClockMux}, bsc.verilog/tasks; 826 checks per
run, and 825 for iverilog which skips one verilator-only check):

| run | pass | fail |
|---|---|---|
| iverilog (reference) | 825 | 0 |
| verilator `--no-timing`, shipped harness (5.020) | 683 | 143 |
| verilator `--no-timing`, new harness (5.020 and 5.051) | 683 | 143 (per-test identical to shipped) |
| verilator `--timing`, new harness (5.051) | 804 | 22 |

Residual `--timing` failure taxonomy (22): ~15 golden diffs whose only
content difference is one or two missing pre-reset/startup display
lines that event-driven simulators emit from X->value transitions at
time 0 (a two-state simulator cannot reproduce these); ~3 diffs that
are pure same-timestamp reordering of display lines across clock
domains (a legal simulator ordering difference); 3 pre-existing golden
diffs that fail identically under `--no-timing`; and 1 Verilator bug
(`$display` of `$signed(sig[msb:0])` printing the unsliced value —
reduced repro exists; surfaces in the timing build of
bsc.verilog/tasks sysModuleDisplay, while the no-timing build of the
same design is unaffected).  Conversely `--timing` fixes the
`$error`/exit-status behavior of sysErrorTest, which fails under
`--no-timing`.  No hangs and no lint failures remain in the sampled
timing runs; under the shipped `--no-timing` flow, several
divided-clock tests hang until killed (never-propagating reset) and
one previously filled the disk with an unbounded VCD.


## Complete failure ledger (composed tree: main + verilator queue + timing)

Every one of the 400 `--timing` failures (Verilator 5.051) is classified;
none are unexplained, and none beyond the 14 noted are caused by the
timing work:

| class | ~checks | notes |
|---|---|---|
| Inout-port designs fail to link | 88 | verilator tristate limitation; plain port rendering does not fix it |
| foreign/BDPI links | 101 | tests hit the use-`-use-dpi` gate; flipping them is a testsuite policy change |
| custom-testbench links (portRenaming, pong, MacTestBench, Amba, options) | ~72 | the no-`main.v` link path; `.ba` foreign in sysGCD |
| `$dumpvar`-warning stdout pollution | ~28 | designs call `$dumpvars` without `$dumpfile`; verilator (both versions) emits a runtime warning line that breaks goldens — fixable with one filter line in `clean_verilator_output` |
| startup X-artifact / never-X lines | ~35 | missing 1-2 pre-reset lines (Hierarchy, positivereset/ClockDividers, mcd Misc/NullCrossing, OVL NeverUnknown, b898); two-state cannot reproduce |
| two-state value semantics | ~7 | divide-by-zero prints 0 not x (divmod), SquareRoot, real/string formatting (parameters/string, DisplayRealLiteral) |
| post-`$finish` activity in `$fwrite` files | 10 | verilator runs one more firing after `$finish`; stdout is truncated by the test driver but `.dat` files are not (all of bsc.misc/fwrite) |
| same-time display ordering | ~5 | interfacecalls, BypassFIFO, plus the slice-verified cases |
| post-5.020 Verilator regressions | ~14 | pass on 5.020, fail on 5.050/5.051 in BOTH modes: the `$signed`-slice display defect (b925, Complex, ArithShift, splitports, sysDivMod, FP ArithPipe, bluesim_vcd), a new runtime `parallel_case` assertion (mutually_exclusive — arguably a real find: the pragma is emitted for non-exclusive rules), and an abnormal exit in `$dumpoff/$dumpon` (verilog/vcd) |
| timing-new: reset-edge startup latching | 11 | gated-clock domains; runtime opt-out `BSC_VLT_NO_RESET_EDGE` |
| timing-new: `--trace --timing` `#0`-init loss | 3 | Verilator regression; avoided by `-dump-formats none` |
| root-run environment (chmod tests) | 3 | known |

Under `--no-timing` the same classes apply plus the ~400 checks that
timing fixes (divided-clock/derived-reset designs and ClockGen builds).
