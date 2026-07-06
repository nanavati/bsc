# incG: BVI member-side checks (increment G / A90, A98)

An `import "BVI"` is a hand-declared boundary, checked against the interface's
`contract_<Ifc>` / `convention_<Ifc>` at the importing package's own compile.
Positive: a ready-less BVI conforms (no ready clause = constant readiness) and
joins a mixed mkOneOf group with generated always_ready members, simulated
under all selections. Negatives: an ungranted declared relation, a declared
ready port against contractAlwaysReady, and claiming a convention-tagged
interface (v0) are each rejected.
