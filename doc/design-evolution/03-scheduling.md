# 03 — Scheduling: One Order, Positions, and Schedules as Values

The scheduling model's destination. RFC-polymorphic-scheduling.md
governs on mechanism; this document states the design and the reasons.

**Status:** v2.0 — 2026-08-24 (Claude). Design only; migration steps
and status live in the RFC's migration sections and the KB lanes,
outside this set.

## 1. The model

Schedules are types, values, and contracts: a permissiveness lattice
on ground schedules; contracts as constraint sets over **position
variables** (a fourth base kind, relational provisos only, no literals
— concrete positions are solver output); subsumption is entailment;
correlation rides shared variables; disjunctive contracts are
antichains of coherent alternatives with non-principality exposed,
never approximated; selection is a value, completion is a near-linear
solve. Positions are the missing *names* of scheduling: they
consolidate by unification (atomicity, calls, ascription), are shared
as sealed-by-default landmarks, and their relationships are
solver-known. Footprints are the contract representation; every
pairwise relation is a derived view; **persist generators, not views**
— materialized pairwise databases are cache poison (T8; the measured
residency blow-up of an eagerly materialized relation database is the
forcing evidence). The model is always a pinned artifact, never
ambient (T3).

DECISION (Ravi): **one order** — the urgency/execution distinction is
dropped; arbitration is positional; fancier arbitration is written
down explicitly. *Why:* two orders made schedules unnameable and
migration untypeable; the expressiveness loss is real but small, and
anything lost is recoverable by stating it. The loss is *measured, not
asserted* — a divergence census names every affected design before the
break ships, and the break itself is a named, versioned event with a
legacy reading mode (the pricing-and-versioning policy is design; the
census mechanics are plan, outside this set).

The strategic converse is on record independently: reorganizing
scheduling around **user-specified schedules** — the compiler *checks*
a stated schedule rather than inferring and imposing one — is the
long-horizon direction, with the note that compatibility between
stated schedules must still be checked, which is exactly what
contracts-as-constraint-sets and verify-mode provide. Named
beneficiary: **interface arguments**, dropped historically because the
compiler couldn't capture their scheduling, return naturally once
footprints ride interfaces as contracts. Schedule certification is
also what makes multiple implementations of one boundary safe (02 §7):
module implementation selection depends on specify-then-check.

## 2. Design rulings around the model

**Engines keep phase machinery; the language keeps one order.**
Sched-then-Exec segments, early-rule passes, and combinational-
schedule exemptions inside engines are *implementation phases
realizing* the single order, not a second semantic order.

**The observable-event contract is language-level.** What must be
defined once, for every engine: when $finish takes effect
(immediately / after action / after rule / after cycle / after
delta), coincident multi-clock guard-snapshot semantics, and the
guard-evaluation-vs-execution split where dynamic alternatives exist.
*Why:* independent per-engine patches can each match one oracle while
disagreeing with each other — three separately-derived finish
alignments proved it. One clause is already stated and emitted:
displays of a timestep flush before $finish commits, and post-finish
statements never execute — realized by emitting finish-carrying task
blocks as named blocks with a `disable` after each $finish, dead code
for simulators that stop at $finish and mandated silence for those
that keep going. The rest of the contract is OPEN (08).

**Dynamic schedules: pin every arm.** Runtime schedule selection never
completes an order at runtime: every coherent alternative is compiled
and validated ahead; dispatch is an ordered guard table with defined
no-match/multi-match semantics; arm tables (order, priority, guard
snapshot point, per-arm coordinates and footprints) join artifact
identity. The compiler is the sole producer of the schedule artifact;
consumers validate every reference — the pinned-model rule applied to
runtime selection.

**Export coordinates; don't reconstruct.** Consumers that need
schedule/execute placement (top-level lifting, auto-fire, engine
binding) read versioned exported coordinates from the canonical
schedule artifact — including within every dynamic alternative — never
lossy reconstruction from late-stage output; reconstruction survives
only as a validation cross-check. Persist decisions (flattened orders,
cycle-break drops, tie-breaks) so a query engine reproduces
compile-time answers by pure lookup.

**Demand-driven disjointness with accounting.** Restricting expensive
pairwise analysis to consulted pairs is sound only with
consulted-pair accounting — a read of an uncomputed verdict fails
rather than defaulting. Where the queries *constitute* the relation,
the design is demand-first with structure-before-solver (complementary
branches, case arms, constructor tags derivable by construction;
scrutinee-bucketed families; a restored effort limit), carrying the
agreement-with-solver test obligation since a disagreement flips a
conflict edge.

**The hardware quadratic is a design lever, not just compile time.**
Priority-chain firing logic is Θ(conflicting-pairs) literals in the
netlist; predictable arbitration and cheap hardware are the same
design choice. Chain/prefix-sharing encodings and per-clique
reporting ride the footprint representation.

**The compile-time quadratic has a measured answer inside the model.**
Reworking scheduling in terms of resources and uses reproduces the
same schedules much faster on most designs (an experimental
implementation exists); resources/uses are footprints by another
name, so the fast scheduler and the persisted contract representation
are one design with one certification, not an independent
optimization.

## 3. The endpoint

The fill dial runs from today's fully-inferred schedules, through
checked partial contracts, to totally-specified (Kôika-style)
schedules verified legal — adopted first where the payoff is highest
(synthesis boundaries, verification-critical blocks), never forced
design-wide. The EHR dissolves into a register observed at named
positions; the FIFO zoo becomes one polymorphic text whose
pipeline/bypass/CF variants are constraint resolutions; the schedule
lockfile joins the build so assembly-time binding is a recorded,
diffable event.

## 4. Pointers

Mechanism: RFC-polymorphic-scheduling.md in full (lattice,
entailment/antichains, positions, landmarks, one order, footprints,
binding time). The open theory is stated there: the no-literals rule,
position scoping across clock domains and synthesis boundaries, the
antichain bet, conjunctive-fragment principality, parametric adequacy,
and the single-position-per-method approximation. Migration steps,
censuses, and status: the RFC and the KB lanes. Provenance: the
meeting-notes digest.

## 5. RESOLUTIONS and OPEN questions

- RESOLUTION: engines' phase machinery is realization, not semantics;
  the observable-event contract is defined once, language-level.
- RESOLUTION: pin-every-arm dynamic scheduling; exported coordinates
  over reconstruction; consulted-pair accounting.
- RESOLUTION: the resources/uses scheduler and the footprint artifact
  are one change.
- OPEN: the remainder of the finish-instant/observable-event contract
  (08 — goldens re-record only after it).
- OPEN: the one-order break's venue and census scope (fork-first vs
  upstream; 08).
- OPEN: the model's stated research risks (coordinate assignment IS
  the scheduling problem; the antichain bet) — if they fail, the arc
  stops at footprints + schedule values + verify mode, which is
  independently valuable.
