# 03 — Scheduling: One Order, Positions, and the Migration

The scheduling model's evolution and its cross-lane resolutions.
RFC-polymorphic-scheduling.md (v0.4) governs on mechanism; this
document records what the holistic review settles around it.

**Status:** v1.0 — 2026-08-24 (Claude, holistic review). Labels: FACT /
DECISION / PROPOSAL / RESOLUTION / NEEDS-RAVI.

## 1. The model (settled)

Schedules are types, values, and contracts: a permissiveness lattice on
ground schedules; contracts as constraint sets over **position
variables** (a fourth base kind, relational provisos only, no literals
— concrete positions are solver output); subsumption is entailment;
correlation rides shared variables; disjunctive contracts are
antichains of coherent alternatives with non-principality exposed,
never approximated; selection is a value, completion is a near-linear
solve. Positions are the missing *names* of scheduling: they
consolidate by unification (atomicity, calls, ascription), are shared
as sealed-by-default landmarks, and their relationships are solver-
known. Footprints are the contract representation; every pairwise
relation is a derived view; persist generators, not views. The EHR
dissolves into a register observed at many points; one polymorphic FIFO
text yields pipeline/bypass/CF by constraint resolution. **The model is
always a pinned artifact, never ambient** (T3).

DECISION (Ravi, 2026-08-23): **one order** — the urgency/execution
distinction is dropped; arbitration is positional; fancier arbitration
is written down explicitly. The loss is measurable: the divergence
census (flag every pair whose final urgency order differs from final
execution order) runs with today's scheduler — over the testsuite plus
a large internal corpus (07) — and names the migration set in advance.

The model has independent strategic confirmation: the longer-horizon
project document (10 §4) names "reorganize scheduling around
user-specified schedules" as the biggest project beyond any roadmap —
the compiler *checks* a stated schedule rather than inferring one, with
the margin note that compatibility between stated schedules must still
be checked (which is exactly what contracts-as-constraint-sets and the
verify mode of step 3 provide). Its named secondary payoff — interface
arguments, dropped historically because the compiler couldn't capture
their scheduling — becomes reachable once footprints ride interfaces as
contracts: record it as a post-migration beneficiary, not a step.

## 2. Resolutions from the review

**R3.1 — The compatibility rung (adopt).** One order is a deliberate
semantic break and gets what breaks get: a named migration rung; fresh
format generations for artifacts whose schedule content changes
meaning; a legacy two-order reading mode for existing artifacts during
transition; the census as its gate; explicit source/artifact mode
selection. Migration step 2's "no semantic change" claim is scoped to
the value-type demotion only. Artifact-graph §14 is synced (or
banner-superseded) to scheduling v0.4 — two documents both labeled
canonical must not describe incompatible contract languages.

**R3.2 — Engines keep phase machinery; the language keeps one order.**
trs's Sched-then-Exec segments, the PG_FINAL early-rule pass (load-
bearing in the CrossingReg parity fix), and Bluesim's combo-schedule
exemptions are *implementation phases realizing* the single order, not
a second semantic order. What must be defined once, cross-engine, is
the **observable event contract**: when $finish takes effect
(immediately / after action / after rule / after cycle / after delta),
coincident multi-clock guard-snapshot semantics, and the guard-
evaluation-vs-execution split where dynamic alternatives exist.
Independent per-engine patches can each match one oracle while
disagreeing with each other (FACT: the $finish #0 fix, the vl_finish
deferral, and Bluesim's complete-the-cycle semantics were three
separately-derived alignments). NEEDS-RAVI: the finish-instant
contract is a language-level decision; goldens re-record only after it.

**R3.3 — Dynamic schedules: pin every arm.** SchedAlt never completes
an order at runtime: every coherent alternative is compiled and
validated ahead (PR #151 already does this — compiled alts), dispatch
is an ordered guard table with defined no-match/multi-match semantics,
and arm tables (order, priority, guard snapshot point, per-arm
coordinates and footprints) join artifact identity. bsc is the sole
producer of the schedule artifact; consumers validate every reference.
This is the pinned-model rule applied to runtime selection.

**R3.4 — Export coordinates; don't reconstruct.** The trs top-level
lift's last-cut Exec placement reconstruction (auto-fire) is replaced
by versioned method schedule/execute coordinates exported in the
canonical schedule artifact (including within every dynamic
alternative); the reconstruction survives as a validation cross-check.
Same law as footprints: persist decisions (flattened orders, cycle-
break drops, tie-breaks) so a query engine reproduces compile-time
answers by pure lookup.

**R3.5 — Demand-driven disjointness with accounting.** The transpose
(PR 47; 25× at 16k rules, byte-identical) restricted the SAT sweep to
consulted pairs with default-false verdicts for the rest. Adopt the
consulted-pair accounting (fail on an uncached read) so no future
consumer can read an uncomputed false. The -sched-conditions layer is
the genuinely separate second step: its queries *constitute* the
relation, so it needs a demand architecture plus structural-before-SMT
(complementary branches, case arms, tag constants derivable by
construction; scrutinee-bucketed families; an effort limit restored) —
with the agreement-with-SMT test obligation, since a disagreement flips
a conflict edge.

**R3.6 — The hardware quadratic is its own rung.** Esposito WILL_FIRE
chains are Θ(conflicting-pairs) literals in the netlist; predictable
arbitration and cheap hardware are the same design choice. Chain/
prefix-sharing encodings and per-clique reporting ride the footprint
representation; this is a scheduling-QUALITY lever, not only speed.

**R3.7 — The compile-time quadratic already has a measured answer.**
FACT (compiler tour, 10 §5): scheduling today considers every rule
pair, and an experimental patch exists reworking it in terms of
resources and uses — same schedules, often much faster, with some
harder cases not yet covered. That patch is a *precursor
implementation* of the footprint representation (step 1): resources/
uses are footprints by another name. RESOLUTION: fold the patch into
migration step 1 rather than landing it as an independent optimization,
so the faster scheduler and the persisted contract representation are
one change with one certification.

## 3. Migration (per the RFC, with the review's additions)

1. Footprint artifact (persist generators; .ba carries footprints,
   decisions, and proven facts; RuleRelationDB and kin become query
   functions — the 18× residency evidence is the forcing function).
2. Schedule value type + the one-order divergence census (RFC step 2)
   **plus the compatibility rung of R3.1**.
3. Verify mode (subsumption checking).
4. Position kind behind a flag; methods bind through callers; internal
   rules existential.
5. Position-polymorphic registers (scalar derived forwarding);
   CReg surface demotes to a derived form.
6. The FIFO demonstration (zoo → one text + frozen-index shims;
   capacity-1-derives-CF as the acceptance test).
7. Assembly-time binding + the schedule lockfile.
8. Kôika mode (total bindings verified legal; data-dependent enables
   per region, opt-in).

Steps 1–3 are independently shippable. The open challenge points stand
as the RFC states them: the no-literals rule, position scoping across
clock domains and synthesis boundaries, and the antichain bet; plus the
lane's open theorems (conjunctive-fragment principality; parametric
adequacy) and the single-position-per-method approximation.

## 4. Lane pointers

RFC-polymorphic-scheduling.md v0.4; RFC-bsc-artifact-graph.md §§14–14.c
(summary; sync pending); "KB: bsc artifact graph" (session arc, ONE
ORDER decision, Codex reviews and adoptions); "KB: bsc polymorphic
scheduling RFC (full text)" (mirror); the scheduling-complexity
addendum (-sched-conditions, hardware quadratic, .ba generators);
fork PR 47; trs PRs #144/#151/#152; "KB: trs top-level lifts + G0129".

## 5. NEEDS-RAVI (rolled up in 09)

- The finish-instant / observable-event contract (R3.2).
- Disposition of the standing Codex queue on this lane: the PR-144/47
  schema recertification set (with 01's registry), the §14 sync, the
  one-order compatibility rung's format generations.
- Whether the transpose goes upstream (B-Lang-org #1087) under the PR
  policy, and the -sched-conditions demand-architecture rung's
  priority.
