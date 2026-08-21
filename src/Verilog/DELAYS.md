# Delay (`#`) idioms in the Verilog primitive library

This is an audit of every delay statement in the primitive library,
classifying each and recording why it is kept.  Context: the
`-vsim verilator` flow builds these files with Verilator, which since
version 5 requires choosing `--no-timing` (delays ignored; the
historical and default mode, with STMTDLY/INITIALDLY lint waived in
`verilator_config.vlt`) or `--timing` (delays honored; selectable with
`BSC_VERILATOR_TIMING=1` or `-Xv --timing`, using
`verilator_config_timing.vlt`).  Event-driven simulators (iverilog,
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

Verilator 5.020 (Debian/apt, 2024-01) crashes (SIGSEGV destroying
coroutine handles) under `--timing` on a process that suspends twice
in one activation with an intervening conditional — e.g.
`begin #0; ...; if (c) begin ...; #0; end ... end` — which is exactly
the shape of the `always@(negedge CLK)` system-task blocks in
BSC-generated Verilog.  A single `#0` in the same position is fine.
Newer Verilator releases fix this (verified on a 5.051-devel source
build); use a recent Verilator for `--timing`.

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
