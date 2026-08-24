# RFC: A portable reset sequence for the simulation harness

Status: draft for discussion
Scope: `src/Verilog/main.v`, `src/Verilator/sim_main.cpp`, the clock
and reset primitives named in "What changes", and testsuite golden
files that record output from the startup window.

## Summary

The testbench reset that bsc's simulation harness provides is currently
asserted *at time 0*, where its effect is not defined by the Verilog
LRM and differs across simulators.  This RFC changes the harness to a
sequence whose outcome is identical, by argument and by measurement, in
four-state event simulators (Icarus Verilog, VCS), two-state simulators
(Verilator), and Bluesim's execution model:

  * time 0: clock low, reset **asserted as a level** (actively driven);
  * time 1: first clock posedge, under reset;
  * times 2..3: one **deassert/assert pulse**, so the assertion is also
    a genuine value **edge**, asynchronously (no clock edge at either
    instant);
  * time 4: reset **deasserted**, between clock edges;
  * steady schedule unchanged: negedge at 5, posedge at 10, period 10.

The clock edge comes BEFORE the pulse deliberately: the pulse is a
one-tick window in which the reset is seen deasserted, and
level-sensitive reset-gated logic (assertion checkers such as the OVL
library) samples during it.  A four-state simulator's X-guards keep
such checkers quiet on uninitialized state; a two-state simulator has
no X, so the window must only ever expose post-reset state -- which
the preceding under-reset clock edge establishes.

Each half of the assertion serves a different simulator class: the
time-0 *level* is what a four-state simulator's initialization
artifacts are judged against (see the ordering argument below), and the
time-3 *edge* is the only thing a two-state simulator or a
`BSV_NO_INITIAL_BLOCKS` build can see at all.  The steady schedule and
every first rule-firing edge (time 10, 20, ...) are unchanged, so
golden files that record post-reset behavior are unaffected.  Golden
files that recorded output from the startup window change; this RFC
argues they were recording a simulator race, not design behavior.

A set of small primitive changes accompanies the harness change; each
follows a rule about clocks and reset that holds on its own (below).

## The problem: time-0 reset assertion is a race

Today `main.v` asserts `RST` in the time-0 inactive region (`#0`).
Three independent defects follow:

1. **It races the rest of time 0.**  Primitive initial blocks
   (`SyncResetA`'s `reset_hold`, `GatedClock`'s gate latch, clock
   generators' outputs) run in the same time-0 inactive region.  The
   LRM does not order initial blocks across modules, nor `#0`
   continuations against always blocks triggered by same-time
   transitions.  Whether a given process observes the reset as already
   asserted at time 0 is scheduler luck.  Golden files recorded under
   Icarus have enshrined one particular resolution.

2. **Two-state simulators cannot see it at all.**  Verilator inputs
   start at 0.  For the (default) negative reset, 0 *is* the asserted
   level, so a time-0 assertion produces no edge, and the asynchronous
   assertion paths (`always @(negedge RST_N)`) never fire.  Derived
   reset domains never reset; divided-clock designs hang.  (The
   verilator harness has carried a compensating hack — an extra
   deassert/assert evaluation pair at time 0 — which this RFC deletes.)
   For positive reset the failure mode inverts but does not improve.

3. **Under `BSV_NO_INITIAL_BLOCKS` there is no reliable assertion.**
   With the initial blocks compiled out, nothing establishes the reset
   network's state until the first clock edge samples the reset level.
   Any flow that removes initial blocks (synthesis-like simulation,
   emulation) starts in an undefined window of unspecified length.

A concrete exhibit for (1)+(2): `bsc.mcd/ClockDividers` `sysClockDiv`.
Its golden contains

    a rl fired at 5, areg = -1431655766

— a rule firing that reads a register still holding the `'hAAAA...`
uninitialized marker, printed from the startup window (the firing is at
real time 0, triggered by a generated clock's initialization edge; see
the clock rule below).  A two-state simulator produces no such line, so
the test cannot pass on both simulators with one golden.

## The principle

The testbench reset is a *contract*, not physics: its only job is to
carry the design from "whatever a simulator starts with" (X, zeros,
`'hAAAA...` markers, nothing) to the design's defined reset state,
**through the design's real reset tree**.  Two consequences:

* **The observable contract starts at each clock domain's first edge
  after that domain's reset deasserts.**  Output produced before that
  is a recording of one simulator's startup artifacts.  Golden files
  must not contain it.

* **The sequence may not rely on anything a simulator class lacks**:
  not on X-edges (two-state simulators have none), not on initial
  blocks (`BSV_NO_INITIAL_BLOCKS` builds have none), not on same-time
  event ordering (the LRM does not define it).

## Why this sequence is deterministic everywhere

**The time-0 level and initialization artifacts.**  In a four-state
simulator, initial blocks run in the first time-0 inactive batch.  A
transition *caused by* those initializations (e.g. a clock output
leaving X) can trigger clocked processes, but any such process resumes
in a *later* batch than the one that triggered it — in particular later
than `main.v`'s own batch-one write of the asserted level.  So every
reset-suppression guard evaluated as a consequence of time-0
initialization deterministically reads "asserted".  This is an
ordering *proof*, not scheduler luck: the read is causally downstream
of the batch containing the write.  (What the time-0 level cannot do is
reach *derived* reset domains — their assertion propagates through
nonblocking updates, which run after the inactive batches.  That gap is
closed by the clock rule below, not by scheduling.)

**External transitions.**  The testbench writes the reset from a
separate process with blocking assignments — the only writes the LRM
leaves unordered against a clock edge at the same instant.  The
schedule therefore keeps them away from clock-edge instants: pulse at
2..3, release at 4; edges at 1, 5, 10.

**Initial-state consistency.**  The primitives' simulation-only initial
values must AGREE with the time-0 asserted level: a reset-holding
register initialized "out of reset" contradicts it, and a two-state
simulator (which sees no edge until the pulse) sits in that
contradiction through the whole startup window -- downstream and
inverted-reset consumers observe a reset network that four-state
simulators (fixed at time 0 by the X -> asserted transition itself)
never show.  The reset-network registers (`SyncResetA`, `SyncReset`,
`ClockSelect`, `UngatedClockSelect` `reset_hold`; the `MakeReset`
family's `rst`) therefore initialize to the value their own
reset/assertion branch produces.  This carries no proof weight -- the
manufactured edge does, and `BSV_NO_INITIAL_BLOCKS` builds work
through the edge alone -- it only removes an init that disagreed with
the sequence.

Consistency also requires the init to be *in effect at time 0*, which
the primitives' traditional `#0` prefix (`initial begin #0; rst = ...`)
silently breaks under Verilator without `--timing`: delays are dropped,
but a statement after even a zero delay resumes in a later evaluation
than the one that ran the initial block, so the C++ zero-initialized
state -- not the init value -- is what the startup window observes.
For a `MakeReset` output, zero *is* "asserted", so consumers saw a
phantom reset of intentionally-unreset state (`mkReset(..., False)`
starts deasserted; `sysResetMux`/`sysResetEither` count in registers
that no reset should ever reach).  The `#0` is therefore stripped from
the reset- and clock-network initial blocks: every value assigned there
is an elaboration constant, and in four-state simulators the only thing
the `#0` ever ordered against -- the same-instant asynchronous reset
branch triggered by the X -> asserted transition -- writes the identical
value, so removing it is benign by value.  (`ClockDiv`'s *functional*
`#0`, inside an always block, is unrelated and stays.)

`InitialReset` is the one primitive where the `#0` must STAY: it has
no reset input -- its own X -> asserted output transition at time 0 is
the assertion edge derived async resets key on, and deferring the init
to the inactive region is what guarantees every consumer process is
already waiting at its event control.  Consistency is restored on the
other side instead: the hold register now uses a polarity-INDEPENDENT
encoding (0 = still asserting), inverted to the reset polarity only at
the output, so the two-state pre-initial value (zero) equals the
initialized value under BOTH polarities.  This matters because a
derived clock can legitimately produce its one assertion-time edge at
time 0 (asserting reset loads a divider's counter, whose top bit may
rise), clocking the hold register in the same instant as the init, in
an order the LRM leaves open across simulators.  In the old value
encoding that race was masked under negative reset -- zero happens to
BE the asserted pattern -- but under positive reset Verilator's shift,
computed from the deasserted pre-initial state, clobbered the init and
the held reset never happened (positive-reset `sysClockDivFifo`'s B
domain counted from its first divided edge).  The encoding change also
removes the testsuite's only manifestation of the upstream Verilator
--trace+--timing initial-`#0` regression: losing an init that writes
the pre-initial value loses nothing.

**Internal asynchronous assertion** (the tree fanning out after time 3)
is race-immune *by dominance*: every consumer's always block checks the
reset level first, and the reset branch writes a value that does not
depend on prior state.  Whatever order the simulator fires the
triggered processes in, "asserted" wins.  Asynchronous assertion is
also *required*, not just safe: clock-generating logic sits upstream of
its own domain's clock and can only be reset without one.

**Propagation through reset synchronizers — and the hardware-model
line.**  The manufactured pulse reaches only consumers wired to the
harness reset itself; a reset synchronizer swallows it.  Its hold
register initializes asserted (initial-state consistency, above), so
the re-assert edge writes the value already held, and the deassert
half can only move the hold register at a clock edge — and the pulse
window is clock-free by construction.  The synchronizer's output
therefore never edges.  This is mostly harmless: any register's reset
clause also applies at its own clock edges by LEVEL, and synchronizers
hold their output asserted for RSTDELAY destination edges past
release, so every clocked consumer resets no later than its first
edge.  The one residual gap is a *read before the destination clock's
first edge*: a fast rule reading a slow-domain async-reset register in
the startup window sees its uninitialized fill, where real
(level-sensitive) async clear holds the reset value and four-state
simulators reproduce that through the time-0 X -> asserted edge
firing the reset branch (`sysClockDiv2`'s crossing register).

Three mechanisms were built or considered for that gap and rejected,
in order, by an explicit DECISION (Ravi, 2026-08-24): **the
primitives model real hardware, and simulation-only behavior does not
belong in their synthesizable semantics.**

* *Pulse regeneration in the synchronizers* (each synchronizer
  re-emitting the deassert/assert pulse on its own output under
  `` `ifdef VERILATOR ``): implemented, validated, and REVERTED —
  it makes harness choreography part of a hardware model.
* *Global `--x-initial-edge`* (Verilator's own four-state
  initialization-edge emulation): rejected on evidence — it
  over-approximates.  A derived signal that initializes to 1 (an
  inverted clock, `~0`) counts as an X -> 1 posedge and ticks
  consumers that four-state's `~X = X` keeps silent (`sysResetInv`
  gained a count; divided-clock streams shifted).
* *Reset-value initialization* (sim-only initial blocks loading
  async-reset registers with their reset values under
  `` `ifdef VERILATOR ``): rejected as a slippery slope — extra
  initialization semantics, however defensible individually,
  accumulate into a parallel semantics.

The accepted disposition: a test that legitimately reads in that
window passes `--x-initial-edge` for itself (`-Xv --x-initial-edge`
at link, verilator-only, documented at the test) — a per-test
simulator knob, not a hardware-model change.  Tests that cannot or
should not are expected-to-differ with the mechanism documented.  The
harness pulse itself STAYS: it is testbench choreography (main.v /
sim_main.cpp), it fires direct async-assert consumers, and
`BSV_NO_INITIAL_BLOCKS` four-state builds rely on its edge alone to
define the reset network.

**Internal synchronized deassertion** changes at destination-clock
edges by design — and is safe there because it is produced by a flop
clocked by that same edge: the new value arrives through a nonblocking
assignment, so downstream logic samples the old (asserted) value at
that edge and first acts on the deassertion one edge later.  Ordinary
synchronous-design determinism, identical in all simulators.

Bluesim needs no change to agree: its model — registers at reset
values, first observable edge after release — is this sequence with the
prelude compressed to zero width.  The event simulators converge to it
from the first post-release edge.

## Two companion clock rules

Harness scheduling cannot reach two artifact sources inside the
primitives; each gets a rule that is independently justified.

**Rule 1 — a free-running clock source makes no time-0 transition.**
`ClockGen` assigned its output at time 0 (`#0; CLK_OUT = initValue`).
In four-state simulation that X -> value assignment is an edge; if
falling, it fires the generated system-task blocks (`always
@(negedge clk)`) of a *derived-reset* domain whose suppression guard
cannot yet read "asserted" (derived assertion is NBA-ordered, after the
guards' inactive-region reads).  Two-state simulators see no edge, so
the simulator classes permanently disagree.  Fix: the output stays X
until the first scheduled edge (`initDelay`) — which is also exactly
the `BSV_NO_INITIAL_BLOCKS` behavior, so the two build flavors converge
as a bonus.

**Rule 2 — a gated clock emits no edges while its reset is asserted.**
`GatedClock`'s transparent-low gate latch tracked its inputs whenever
`CLK_IN` was low.  During the reset window a four-state simulator holds
the latch anyway (`CLK_IN` is still X, and `!X` is not true), but a
two-state simulator's `CLK_IN` is a real 0, the latch is transparent,
and the gate can open in time to pass the under-reset clock edge into
the gated domain — one extra edge that unreset (`mkRegU`) state
observes forever.  Fix: force the gate closed while `RST` is asserted
(the port already exists).  This makes the two simulator classes
identical by construction, matches the behavior existing goldens
recorded, and defines the gate under `BSV_NO_INITIAL_BLOCKS` from the
assertion edge onward.

**A companion task rule — `$finish` defers behind the timestep's
output.**  Every generated system-task block opens with `#0`, so all of
a timestep's display blocks resume together in the first inactive
batch — in an order the LRM leaves unspecified.  A `$finish` in one
module's block (a `done` rule) racing display output in another's is
therefore simulator luck: an event-driven simulator that resumes the
finish first terminates mid-timestep and the other block's line is
never printed.  Two changes make the end of simulation deterministic:

* The compiler emits one more `#0` immediately before `$finish`
  (inside its own guard, so cycles that don't finish pay nothing).  In
  an event-driven simulator displays flush in batch one and the finish
  runs in batch two — the order becomes a property of the text rather
  than of the scheduler, consistent with Bluesim, which completes the
  cycle's actions before stopping.  iverilog happened to flush
  displays first already, so its output is unchanged.  This is emitted
  unconditionally (not under `` `ifdef VERILATOR ``).

* Verilator needs two more steps, for a different reason: it does not
  terminate execution at `$finish`.  First, its default `vl_finish`
  prints the "`Verilog $finish`" notice the moment the task executes —
  and its zero-delay rounds interleave with cross-module signal
  propagation, so the notice can legally land *ahead* of same-slot
  display output on stdout (`sysTestMkClock`, `sysNullSyncTest2`: the
  testsuite truncates output at the notice line and the last display
  vanished from the comparison).  The harness (`sim_main.cpp`, via
  `-DVL_USER_FINISH`) now records the `$finish` and prints the
  identical notice after the last eval, where a trailer belongs.
  Second — exposed by that relocation — the finishing *process itself*
  keeps running: statements after a taken `$finish` in the same
  system-task block (a whole clock domain's tasks share one block, so
  any rule scheduled after the done rule qualifies) execute to the end
  of the time slot and print output no event-driven simulator shows;
  the old mid-stream notice had been *accidentally* truncating exactly
  there.  The compiler therefore emits every finish-containing task
  block as a NAMED block with `disable <label>` immediately after each
  `$finish`: dead code for simulators that stop at `$finish`, the
  mandated silence for those that keep going.  Emitted
  unconditionally — the same text works everywhere.

One four-state artifact remains recorded in a shared golden and is
*not* emulated: an initially-closed gated clock leaves X at time 0,
whose falling edge fires an unguarded (`mkRegU`-domain) display block
once before any real clock edge (`sysGatedClockCycle`).  A two-state
clock output starts at a solid 0 and cannot produce a time-0 negedge;
any manufactured pulse would first *rise*, falsely clocking
gated-domain registers whose enables do not include the gate.  That
compare is marked expected-to-differ under Verilator instead, with the
mechanism documented at the test.

## What changes, concretely

* `main.v`: the initial block's reset choreography (shown above).
  `BSV_LEGACY_RESET` restores the previous choreography for one
  release, as a migration aid for environments with startup-window
  goldens.
* `sim_main.cpp` (verilator): the same schedule in both `--timing` and
  `--no-timing` builds; the time-0 deassert/assert evaluation hack and
  its `BSC_VLT_NO_RESET_EDGE` escape are deleted.
* `ClockGen.v`, `ClockDiv.v`, `GatedClockDiv.v`, `MakeClock.v`:
  rule 1 (no time-0 output transitions).  `GatedClock.v`,
  `GatedClockDiv.v`: rule 2 (gate closed under reset).
* `SyncResetA.v`, `SyncReset.v`, `ClockSelect.v`,
  `UngatedClockSelect.v`, `MakeReset{,0,A}.v`: initial state agrees
  with the time-0 asserted level (initial-state consistency, above).
* Tests that read async-reset state before the destination clock's
  first edge pass `--x-initial-edge` per-test under verilator
  (propagation through reset synchronizers, above; the synchronizer
  primitives themselves are unchanged by DECISION).
* The compiler emits `#0` before `$finish` in the generated
  system-task blocks, and the verilator harness defers the `$finish`
  notice line to after the last eval (companion task rule, above).
* The `#0` prefix is stripped from the initial blocks of the reset- and
  clock-network primitives (the two families above plus `ClockDiv`,
  `GatedClockDiv`, `GatedClock`, `ClockMux`, `UngatedClockMux`,
  `ResetMux`, `GatedClockInverter`), so the inits are in effect at
  time 0 under no-timing Verilator (initial-state consistency, above).
* `InitialReset.v`: the hold register moves to a polarity-independent
  encoding so its zero pre-initial state means "asserting" under both
  polarities; its `#0` stays (initial-state consistency, above).
  Output timing is unchanged in both polarities.
* Three multi-domain tests whose goldens interleave same-instant
  `$display`s (`sysRstTest` x3 in both reset polarities,
  `sysSyncFIFOCountTest`) adopt the testsuite's existing
  sorted-comparison convention, since the LRM does not order
  same-instant output across separately-triggered processes.
* Testsuite goldens that recorded startup-window output are re-recorded
  once — identically valid for every simulator.

## What does NOT change

* The steady clock schedule (negedge 5, posedge 10) and therefore all
  timestamps in post-reset output.
* The `'hAAAA...` uninitialized-register markers: they remain the
  visible detector for state that no reset ever reaches.
* Bluesim.

## Evidence

(measured on this branch, per-test; Icarus 12.0, Verilator 5.051)

* `sysClockDiv` (mkAbsoluteClock + AsyncResetFromCR + divided domain):
  Icarus and Verilator `--timing` byte-identical; the only golden
  change is the removal of the startup-artifact line quoted above.
* `sysGatedClock_OneMod` (gated clocks, unreset registers): Icarus and
  Verilator byte-identical AND matching the existing golden — no
  re-record needed; before rule 2 the two simulators disagreed on every
  line (one extra gated edge in the two-state run).
* Full testsuite, Icarus 12.0: **18,828 pass / 4 fail / 129 xfail** —
  every failure pre-existing and environmental (two chmod-as-root
  tests, DupInclude, one VCD truncated by the harness file-size
  ulimit).  The reference simulator is fully green on the new
  contract.
* Full testsuite, Verilator 5.051 (automatic per-design timing):
  **18,626 pass / 40 fail / 237 xfail**, down from 79 failures before
  this branch.  The 40 decompose completely:
  - 12 upstream Verilator defects/behavior: the $signed-slice display
    regression (6 checks), the trace+timing initial-#0 regression (3,
    all in positivereset/Reset), and the parallel_case runtime
    assertion (3);
  - 6 custom-testbench link failures (bsv_examples/MacTestBench),
    a pre-existing flow gap unrelated to reset;
  - 7 same-instant display-ordering differences (sysRstTest x2
    polarities, sysSyncFIFOCountTest) — candidates for the testsuite's
    sorted-comparison convention;
  - 9 residual four-state startup differences (one extra
    X-window edge or print in specific derived-clock paths:
    sysClockDiv2's crossing register, sysClockDivFifo/2,
    sysTestMkClock's tail count, sysNullSyncTest2's duplicated line,
    sysGatedClockCycle) — the continuing primitive audit;
  - 3 flips *introduced by the initial-state-consistency fix itself*
    (sysResetMux, sysResetEither, SpecialSyncReg): Verilator now
    resets these designs correctly while Icarus's X-passthrough
    preserves the old never-reset behavior their goldens recorded —
    the ResetMux/ResetEither select paths are the audit's next round;
  - 3 environmental (chmod-as-root, DupInclude), simulator-independent.
  One XPASS marks an XFAIL screen now too broad.
* Audit round (the ResetMux/ResetEither flips), same tree plus the
  `#0` strip and the sorted comparisons: the "flips" diagnosis above
  was wrong — instrumentation showed Verilator *phantom-resetting*
  intentionally-unreset state because the `#0`-deferred init left C++
  zeros (= asserted, for a `MakeReset` output) visible through the
  startup window; the recorded never-reset goldens were correct
  behavior all along.  After the strip, a 14-directory matrix covering
  every affected directory (mcd Reset/SyncReset/LevelFifo/ClockDividers/
  Misc/NullCrossing/Gating/ClockMux/Hierarchy/MakeClock, positivereset
  ClockDividers/SyncReset, SpecialSyncReg, OVL): Icarus **0 fails in
  all 14**; Verilator check-level failures in these directories fall
  **19 -> 10**, the nine fixed being exactly the two flips, the six
  sysRstTest ordering checks, and sysSyncFIFOCountTest, with the
  survivors byte-identical to before (no regressions).  The ten
  survivors are sysClockDiv2 (x2 checks), positive-reset
  sysClockDivFifo (x2) and sysClockDivFifo2 — the negative-reset
  versions now pass — sysTestMkClock/sysTestMkUngatedClock,
  sysNullSyncTest2, sysGatedClockCycle, and SpecialSyncReg's
  fast_to_slow (a divided-clock startup-phase shift, reclassified into
  the residual-startup class).  Full-suite confirmation on the final
  tree: Icarus unchanged at 18,828 / 4 / 129; Verilator **18,635 pass /
  31 fail / 237 xfail** (= 40 - 9), decomposing as 12 upstream
  (6 $signed-slice + 3 trace+timing + 3 parallel_case) + 6 MacTestBench
  link + 10 residual startup + 3 environmental — the
  same-instant-ordering and flips classes are now empty.
* Audit round 2 (the positive-reset-only `sysClockDivFifo` asymmetry),
  same tree plus the `InitialReset` encoding change: probing the reset
  network showed the mechanism described under initial-state
  consistency above (Verilator's time-0 divided-clock edge clobbering
  the value-encoded hold init under positive reset only).  A
  14-directory matrix over every affected directory: Icarus 0 fails in
  all 14 (byte-unchanged by the fix); Verilator fixes 6 checks --
  positive-reset `sysClockDivFifo` (x2) and `sysClockDivFifo2`, and
  all 3 positivereset/Reset checks previously attributed to the
  upstream --trace+--timing regression (the bug still exists upstream,
  but with the init writing the pre-initial value there is nothing
  left for it to lose) -- with every survivor byte-identical.
  Full-suite confirmation on the final tree: Icarus unchanged at
  18,828 / 4 / 129; Verilator **18,641 pass / 25 fail / 237 xfail**
  (= 31 - 6); upstream class 12 -> 9 ($signed-slice 6, parallel_case
  3), residual startup 10 -> 7 (sysClockDiv2 x2, sysTestMkClock x2,
  sysNullSyncTest2, sysGatedClockCycle, fast_to_slow).

## Migration

Downstream users with their own goldens: output timestamps are
unchanged; only output printed before a domain's reset completes
changes (for startup artifacts, disappears).  `-D BSV_LEGACY_RESET`
restores the old harness behavior for one release.  Designs that relied
on a rule firing before reset (reading uninitialized state) were
observing the race; there is no compatible way to keep that behavior on
a two-state simulator.

## Future work (out of scope here)

* VCS validation (same four-state semantics as Icarus; expected to
  match by the region-ordering arguments above).
* Bluesim bootstrap: execute the same sequence through Bluesim's
  dynamic reset machinery with registers constructed
  pattern-until-reset, making the init pattern a knob (`aa` | `zero` |
  `random:<seed>`); gives Bluesim the same missing-reset visibility and
  enables initialization-sweep testing.
* Auditing the remaining clock-source primitives (dividers, muxes,
  selectors, MakeClock) against rules 1 and 2; this branch fixes the
  ones the testsuite exercises into disagreement.
