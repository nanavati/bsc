# bsc.boundary/p3

Behavioral tests for boundary-architecture phases 1-3: introspectable
`signature_<flatifc>` defs; declared interface contracts
(`contract_<Ifc>`) checked at each implementation's own compile, with
positioned errors for violations and malformed contracts; and
implementation groups (`mkOneOf`), covering Verilog `BSV_IMPL_*` macro
selection, Bluesim `-use-impl` selection, the `impls.json` selection
manifest, group-formation negatives, and a cross-package group.
