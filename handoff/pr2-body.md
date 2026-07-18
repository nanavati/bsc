## Summary

Port properties (`clock`, `reset`, `reg`, `const`, `unused`, `inhigh`,
...) are now derived by `getIOPropsA`, a semantic analysis of the
`APackage` and the schedule, instead of being measured off the optimized
netlist at the end of the Verilog backend. A property is asserted only
when it is entailed by the design's structure, dataflow, and schedule —
so the answers are stable across optimization settings, inlining
settings, and backends. The results feed the import-BVI wrapper
attributes in the `.bo` for **both** backends (Bluesim compiles gain
port properties, closing the long-standing `XXX` in `bsc.hs`) and the
Verilog "Ports:" comment. The old `getIOProps` remains available for
comparison behind `-dIOproperties`, computed only when that dump is
requested.

A design document (`doc/proposals/port-properties.md`) records the
property definitions, the soundness/stability contracts, the validation
evidence, and the migration plan (this PR is steps 1–3; steps 4–5 retire
`getIOProps` after a release of coexistence).

Based on the `getIOProps` inout fix PR, whose commit this branch
contains; it can be rebased once that merges.

## Why

The measured properties are functions of a particular compile, not of
the design: an unused input clock loses its `clock` label because no
surviving netlist connection witnesses it; `-no-inline-rwire` makes a
value read through a bypass wire lose its `reg` label although the
connectivity is unchanged; a ready can be `const` only because of a CSE
rewrite. The properties are recorded in the `.bo` and consumed by
parent compiles (`inhigh` legality, readiness reasoning), so the
instability propagates up the hierarchy.

## How it works

- Ports are enumerated exactly as `AState` constructs them.
- Structural roles (clock/gate/reset/inout, declared props) come from
  the wire/field info and are always present — an unused input clock is
  `clock unused`.
- `reg`/`const`/`unused` are deduced by dataflow: wire and CReg
  instances are looked through regardless of the inlining flags; a
  memoized evaluator folds schedule-time constants (never/always-firing
  WILL_FIREs, wire validity, complementary conditions); and the argument
  muxes of state-instance methods are modeled with AState's own port
  allocation, exclusivity test, and order — for action methods and value
  methods (RDY-based selectors for interface value-method users). The
  references AState itself creates for a caller's WILL_FIRE are folded
  semantically: enables absorbed by constant or complementary conjuncts,
  selectors of direct connections, losing arms, and last mux arms
  (absorbed into don't-care defaults).
- Merges are crossed by agreement, not enumeration: equal expressions
  collapse; value sets are never enumerated. This boundary is what makes
  the answers stable (see the design document).

## Validation

- Sweep of all 2124 code-generating testsuite designs (~18,300 port
  lines) comparing both analyses: identical port enumeration everywhere;
  1,686 lines differ, of which 1,638 are the richer structural labels,
  15 are strictly more accurate (dead-logic `unused`, CReg port-0 `reg`,
  a register repacked through an identity case), and 33 are the
  documented boolean-minimization non-goal. No line asserts a property
  `getIOProps` contradicts.
- Stability demonstrated under `-no-inline-rwire`, `-no-inline-creg`,
  `-keep-fires`, where the netlist measurement weakens.
- `testsuite/bsc.verilog/portprops`: golden tests dumping both analyses
  side by side cover each deduction mechanism, including new tests for
  value-method argument muxes (`APkgProps_VMux`) and enable/selector
  folding (`APkgProps_EnFold`); 73/73 pass.
- Full dejagnu testsuite: golden Verilog "Ports:" comments regenerated;
  a further ~15 goldens whose `compare_verilog` checks require a Verilog
  simulator (dormant otherwise) were regenerated — their name-counter
  drift predates this branch, verified with the pre-change compiler.
  Remaining failures are only the tests requiring unreadable files while
  running as root.
- Cross-backend: a child compiled with `-sim` and a parent with
  `-verilog` — the parent deduces its input `unused` from the child's
  `.bo`.
- Tractability: memoized per definition; no measurable overhead on the
  largest testsuite design (h264 deblocking filter).

## Questions for reviewers

1. Is `doc/proposals/` an acceptable home for the design document?
2. Naming: `-dAPackageIOproperties` / `getIOPropsA`.
3. Timeline for migration steps 4–5 (retiring `getIOProps`).
