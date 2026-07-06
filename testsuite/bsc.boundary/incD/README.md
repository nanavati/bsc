# incD: declared method conventions (design doc A96)

Behavioral tests for `convention_<Ifc>` declarations
(`Prelude.ConventionStmt`, `conventionReadyValid`).  The convention
def is read at each member's own compile (`bsc.hs`:
`declaredConventions`); the tagged Action method's execute condition
is gated with its own ready (`AAddScheduleDefs.gateRV` — transfer on
request AND ready) and `VPreadyvalid` is stamped on the enable port
(visible in a group's selection manifest as
`enable-props:readyvalid`).

Files:

- `DeclRV.bsv` — interface `Pusher` with Action method `req` tagged
  `conventionReadyValid`; the generated `.v` gates the state update:
  `v$EN = EN_req && !ph`.
- `DeclClassic.bsv` — the contrast member (same body, no convention):
  classic enable `v$EN = EN_req`.
- `DeclPair.bsv` — interface `Counter` with a contract and a
  convention; two members `mkCounterOnes` / `mkCounterTwos`, both
  stamped from the one declaration (conformance by construction).
- `TopDeclPair.bsv` — parent forming a group over both; simulated on
  both backends with the default root
  (`sysDDeclPair.out.expected`) and with the alternate selected
  (Verilog `-D BSV_IMPL_c_twos`, Bluesim `-use-impl c=twos`;
  `sysDDeclPair.twos.out.expected`).
- `DeclUnknown.bsv` — convention names an unknown method: positioned
  error (S0015) at the member's compile.
- `DeclValue.bsv` — `conventionReadyValid` on a value method (no
  request wire): positioned error.
- `DeclAE.bsv` — `conventionReadyValid` combined with the
  `always_enabled` pragma for the same method: positioned error (a
  tied-high request is a different convention).

All expected outputs and message fragments were frozen against a live
run of this tree's compiler.
