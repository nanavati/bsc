# RFC: A portable reset sequence for the simulation harness

Status: draft for discussion
Scope: `src/Verilog/main.v`, `src/Verilator/sim_main.cpp`,
`src/Verilog/ClockGen.v`, `src/Verilog/GatedClock.v`, testsuite golden
files that record output from the startup window.

## Summary

The testbench reset that bsc's simulation harness provides is currently
asserted *at time 0*, where its effect is not defined by the Verilog
LRM and differs across simulators.  This RFC changes the harness to a
sequence whose outcome is identical, by argument and by measurement, in
four-state event simulators (Icarus Verilog, VCS), two-state simulators
(Verilator), and Bluesim's execution model:

  * time 0: clock low, reset **asserted as a level** (actively driven);
  * times 1..2: one **deassert/assert pulse**, so the assertion is also
    a genuine value **edge**, asynchronously (no clock edge at either
    instant);
  * time 3: first clock posedge, under reset;
  * time 4: reset **deasserted**, between clock edges;
  * steady schedule unchanged: negedge at 5, posedge at 10, period 10.

Each half of the assertion serves a different simulator class: the
time-0 *level* is what a four-state simulator's initialization
artifacts are judged against (see the ordering argument below), and the
time-2 *edge* is the only thing a two-state simulator or a
`BSV_NO_INITIAL_BLOCKS` build can see at all.  The steady schedule and
every first rule-firing edge (time 10, 20, ...) are unchanged, so
golden files that record post-reset behavior are unaffected.  Golden
files that recorded output from the startup window change; this RFC
argues they were recording a simulator race, not design behavior.

Two small primitive changes accompany the harness change; each is a
rule about clocks and reset that holds on its own (below).

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
1..2, release at 4; edges at 3, 5, 10.

**Internal asynchronous assertion** (the tree fanning out after time 2)
is race-immune *by dominance*: every consumer's always block checks the
reset level first, and the reset branch writes a value that does not
depend on prior state.  Whatever order the simulator fires the
triggered processes in, "asserted" wins.  Asynchronous assertion is
also *required*, not just safe: clock-generating logic sits upstream of
its own domain's clock and can only be reset without one.

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

## What changes, concretely

* `main.v`: the initial block's reset choreography (shown above).
  `BSV_LEGACY_RESET` restores the previous choreography for one
  release, as a migration aid for environments with startup-window
  goldens.
* `sim_main.cpp` (verilator): the same schedule in both `--timing` and
  `--no-timing` builds; the time-0 deassert/assert evaluation hack and
  its `BSC_VLT_NO_RESET_EDGE` escape are deleted.
* `ClockGen.v`: rule 1.  `GatedClock.v`: rule 2.
* Testsuite goldens that recorded startup-window output are re-recorded
  once — identically valid for every simulator.

## What does NOT change

* The steady clock schedule (negedge 5, posedge 10) and therefore all
  timestamps in post-reset output.
* The reset primitives' logic and initial values (`SyncResetA` is
  untouched; its deasserted init no longer matters to the outcome,
  because the load-bearing assertion is the time-2 edge).
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
* Full-testsuite validation table: appended at the end of this
  document when the runs complete.

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
