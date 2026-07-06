# incC: contractAlwaysEnabled (design doc A90)

Behavioral tests for the `contractAlwaysEnabled` contract statement
(`Prelude.ContractStmt`).  The clause is a *consumer assumption*: it
imposes nothing on a member at its own compile.  It takes effect when
a member's boundary is sealed at group formation (`mkOneOf` /
`primMkGroup`): sealing stamps `VPmusthigh` on the method's enable
port (`ContractCheck.markMustHigh`, called only from `IExpand`'s
`PrimMkGroup` handler), which keys the existing always-enabled
`ProveEq` obligation at each instantiating parent's own compile
(`AAddScheduleDefs.handleSubmodAlwaysEnabled`); an inconclusive proof
is warning `G0015` (`EEnableNotHigh`), promotable to an error with
`-promote-warnings G0015`.

Files:

- `Pulse.bsv` — interface `Pulse` (`method Action tick`), contract
  `contractAlwaysReady("tick")` + `contractAlwaysEnabled("tick")`,
  members `mkPulseA` (root) and `mkPulseB` (alternate).
- `TopGood.bsv` — group parent driving `tick` every cycle: clean
  compile, simulates on both backends (`sysCTopGood.out.expected`).
- `TopCond.bsv` — group parent driving `tick` conditionally: warning
  `G0015` at the parent's compile.
- `TopCondErr.bsv` — same design, separate module, compiled with
  `-promote-warnings G0015`: fails (a separate file because `bsc -u`
  skips regeneration of up-to-date output).
- `TopDirect.bsv` — direct (non-group) instantiation of the same
  member, driven conditionally: no obligation, no `G0015` (the stamp
  happens at group formation only).
- `PulseNoAR.bsv` — `contractAlwaysEnabled` without
  `contractAlwaysReady` for the same method: positioned error (S0015)
  at sealing.
- `PulseValAE.bsv` — `contractAlwaysEnabled` on a value method:
  positioned error (S0015) at sealing.

All expected outputs and message fragments were frozen against a live
run of this tree's compiler.
