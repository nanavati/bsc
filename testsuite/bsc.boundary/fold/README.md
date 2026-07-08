# The fold as producer, widened (increment 8)

Under the hidden `-boundary-fold` flag the wrapper's
interface-rendering body is built from the module's
`boundary_<flatifc>` description instead of re-walking the pragma
tables.  Increment 7's pilot covered flat method-only interfaces;
increment 8 widens the description-directed walk to every shape the
suite synthesizes:

- **subinterfaces** (`HierFold.bsv`) — the walk recurses with the
  inventory's structure, consuming dotted-path entries in the DFS
  order the emission produced them; a renaming `prefix` on the
  subinterface field flows through the description's slots;
- **vectors of subinterfaces** (`VecFold.bsv`) — the description
  carries one entry per concrete position with the index-erased
  `[_]` path (one shared WrapField codec, the upstream index-erasure);
  the fold re-expands them to `items_0_*`, `items_1_*`, `items_2_*`;
- **clock/reset/inout members** (`ClkFold.bsv`, `InoutFold.bsv`) —
  opaque entries (native floor, no codec) now carry the naming slots
  so the fold renders their `saveFieldPortTypes` too;
- **renamed ports** (`RenamedFold.bsv`) — `prefix`/`result` method
  attributes reach the boundary only through the description;
- **always_ready on the interface** (`ArFold.bsv`) — the minted
  `AR_` flat type's description drives a boundary with no RDY ports.

Increment 9 adds type verification: each field entry's resolved
method type (recovered from the `f`-typed proxy the typechecker
instantiated at the declaration) must equal the member's own
inventory type before the fold may fire — `XPkgIfc.bsv`/
`XPkgUser.bsv` prove this across a package boundary, where the
types were recorded at one compile and verified at another.

Each shape asserts a `fold <module>` line in the
`BSC_BOUNDARY_FOLD_LOG` decision log and the absence of any
`fallback`; `FoldTb.bsv` links and runs on Bluesim under the flag.
The defensive posture is unchanged: any description/inventory
disagreement (naming, kind, arguments, or types) falls back silently
to the legacy walk — and is a positioned error under
`-check-wrap-shadow` — so a stale description can never change the
produced wrapper.
