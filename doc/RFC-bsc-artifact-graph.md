# RFC: The bsc Artifact Graph

Cache-seam decomposition, contracts, and the build.

**Status:** Draft v0.7 — strawman distilled from a design discussion
(Ravi Nanavati with Claude), 2026-08-23. Not proposed upstream; the
sections stand independently and are separable into individual proposals.
v0.2 added: the ba as witness (connect, not conflate); clocks and resets
under the semantic/physical split. v0.3 added: import strata. v0.4 added:
§13, the relation to the post-GenWrap design (July 2026). v0.5 added:
§14 schedule polymorphism and the first draft of §15. v0.6 rewrote §15
around the correctly identified target — the pre-.bo eager layer
(LiftDicts / fixupDefs / iSimpDicts / iSimplify) — with auto-boundary
demoted to §15.b. v0.7 adds: §14.b schedules as values (the Kôika precedent).

---

## 1. Summary

bsc's long-run decomposition should be organized around **cache seams,
not process seams**: a vocabulary of typed, content-addressed artifact
kinds ("nodes") with pure derivations between them, orchestrated by a
dynamic build system (Shake), with process boundaries demoted to a
per-node deployment choice. Under this organization:

- `bsc -u` is replaced by a small external Shake driver that gets
  parallelism, content-hash staleness, and early cutoff for free.
- The staged flow stops being a compiler mode and becomes node
  granularity (an interface artifact completing early unblocks importers).
- Separate compilation is expressed by **contracts**: promises a parent
  elaborates against, with implementations bound later. Contracts are
  ordinary elaboration-time **values**, so they ride the existing
  package/import machinery.
- A contract further splits into a **semantic layer** (types, scheduling,
  clocking relationships between Bluespec-level objects) and a
  **physical realization layer** (the mapping of Bluespec entities to
  ports and port relationships). Parents elaborate against the semantic
  layer only; netlist composition consumes the physical layer at link
  time — for every backend, Verilog included.
- Demand-driven instance-specific synthesis (polymorphic specialization)
  falls out of the same machinery: a specialization request is an
  elaboration-time contract value whose canonical serialization is the
  cache key of the node that provides it.

## 2. Motivation

This design emerged backwards, from build/test mechanics toward language
semantics. The observations that forced it:

- `bsc -u` is a sequential mini-make with timestamp staleness and blind
  recompile propagation (`Depend.chkDeps` / `needsUpd` /
  `compile_with_deps`): an import marked for recompilation forces yours
  even when its output is unchanged. No parallelism, no cutoff.
- The compile pipeline already fuses artifacts that want independent
  identities: a `.bo` holds signature + ISyntax bodies; a `.ba` holds an
  elaborated module whose boundary information is re-derived per session
  by every parent; `VModInfo` fuses semantic promises with physical port
  facts.
- The testing matrix is growing multiplicatively (backends × simulators
  × engines × combined/separate modes × BVI import paths) and its new
  assertions are differential (cell vs cell), which a static run-level
  approach pays for linearly with full recompiles per cell.
- Demand-driven specialization — elaboration discovering it wants a
  particular polymorphic instance as a separately compiled, shared
  artifact — is a *suspending build* problem that static graphs
  (make, Bazel) cannot express and Shake expresses natively.

## 3. A Shake driver replacing `-u`

An external driver (another executable in the cabal package) whose
`%.bo` rule: need the source; scan imports **with the compiler
library's own scanner** (`Depend.parseFile` — zero scanner drift); need
the imported `.bo`s (Shake recurses through the discovered graph); run
plain `bsc` on the one file. This is the ghc-make shape; a few hundred
lines.

Delivered over `-u` and over make:

- **Parallelism across the DAG width** (`shakeThreads`).
- **Content-hash staleness** instead of timestamps.
- **Early cutoff**: a recompiled-but-identical `.bo` stops the
  recompilation wave. v1 keys on the whole `.bo` hash (cross-module
  inlining reads bodies); signature-level cutoff arrives with the
  iface/impl split (§6), making the driver the delivery vehicle for the
  staged-flow / early-`.bo` critical-path line.

Checklist items: flags become oracle keys (partitioned per node kind —
a Verilog-only flag must not invalidate typechecking); search-path
lookups go through tracked existence probes (**negative dependencies**:
the absence of a file earlier in `-p` is load-bearing; untraced probes
mean stale hits when a shadowing file appears); a one-time
hash-stability audit of `.bo` output for identical inputs; and bsc runs
**without** `-u` under the driver — one staleness engine, never two.

The in-process variant (bsc embedding Shake, parallel package compiles
in one process) is *not* modest: global mutable state (string interning
among it) makes package compilation non-reentrant today. External
driver first; a persistent-daemon variant only if per-process `.bo`
reloading measures as dominant.

The driver doubles as the seed of a future testsuite orchestrator and
as the rail demand-driven specialization runs on (§9), but pays for
itself immediately: every Makefile-plus-`-u` user gets parallel builds.

## 4. Containment in a static-graph build (Bazel)

If bsc goes Shake-native with demand-driven synthesis as the feature a
static graph cannot match, it can still be *contained* in Bazel by four
composable patterns, each with industrial precedent:

- **(A) Design-scoped black-box actions with tree-artifact outputs.**
  Unknown outputs are legal via declared directories; unknown inputs are
  over-approximated to the transitive source closure (which a scanner
  already computes). Hermetic, remote-cacheable at design granularity.
- **(B) Persistent worker** keeping bsc-shake warm across actions
  (the rules_scala/zinc precedent: an internally-incremental compiler
  inside Bazel).
- **(C) Back the internal share with the remote-cache CAS (REAPI).**
  The sccache-with-shared-storage trade, sound given deterministic keys.
  Restores cross-design specialization dedup that Bazel cannot see, and
  makes pattern A's over-approximated invalidations cheap: reruns become
  internal cache hits end to end.
- **(D) The lockfile pattern.** The specialization set is discovered
  dynamically but is a deterministic function of the sources and drifts
  rarely; pin a generated specialization manifest that declares real
  targets, with a refresh action when the demand set drifts
  (crate-universe / gazelle precedent).

Worst case is instructive: duplicating specialization work inside each
design's action and never deduplicating is the C++ template/linker
model — which is bsc's *status quo* (full elaboration per design).
Containment never does worse than today.

Hooks to design into bsc-shake early because they are painful to
retrofit: deterministic keys; a **frozen/manifest mode** (given a closed
input set, either complete or fail with a machine-readable list of
missing specialization requests — this one feature enables pattern D,
CI refresh loops, and every static-graph integration, and doubles as
the restart-based specialization protocol); a **pluggable share
backend** (directory or REAPI); a self-contained declared-output-tree
mode.

## 5. Cache seams, not process seams

The utility-split question "which phases become separate executables?"
is a process decomposition. The prior question is "what are the
**nodes**?" — the units of demand, keying, cutoff, and sharing. Once
orchestration is a dynamic graph, bsc decomposes into typed
content-addressed artifact kinds with pure derivations, and process
boundaries become a per-node deployment choice — heap isolation for
20–30 GB elaborations, global-state safety, distribution — decided
*after* the artifact graph. This is the query-based compiler
architecture (salsa / rust-analyzer, rustc's red-green incrementality,
Rock) with the queries made durable. bsc's natural grain —
package/module/instance rather than expression — is what makes it
practical in batch.

A sequencing discipline governs every refactor in this RFC: **never
delete a coarse artifact kind until the finer nodes that replace its
role exist and carry the demand.**

## 6. The node vocabulary

A candidate earns durable-node status by **cutoff potential** (output
more stable than inputs) *or* **fan-out dedup** (multiple consumers),
plus serialization cheaper than recompute and a definable canonical
form. Against the actual pipeline (symtab → derive → CtxRed → typecheck
→ IConv → `.bo` → IExpand → A-passes/scheduling → `.ba` → backends):

| Candidate | Verdict | Notes |
|---|---|---|
| parsed CSyntax | **node** (dedup) | Zero cutoff, real fan-out: the dependency scan is a full parse today; one parsed node serves scan + front end + tooling. |
| desugared CSyntax | phase | Already import-dependent; key ≈ typecheck's. |
| **iface(pkg)** | **node** | The anchor: exported types/classes/instances/value sigs with raw telescopes, fixities, pragma surface. Emitted at end of typecheck (unsigned exports need inference). Body edits leave it unchanged → importers cut off. v2: per-declaration fingerprints. |
| typecheck result | rule with two outputs | One front rule (typecheck+IConv over the parsed node) emits iface and impl; nothing parses or typechecks twice. Its *diagnostics* are first-class output regardless. |
| **impl(pkg)** | **node** | Today's `.bo` second half: ISyntax bodies for cross-module inlining. v2: per-definition impl nodes, demanded only when actually inlined — dynamic independence at definition grain, pointless under make, natural under Shake. |
| **semcontract(inst)** | **node** | §8/§10. What a parent's elaboration needs of a child. Cheap, stable. |
| **realization(inst)** | **node** | §10. What netlist composition needs: the physical face. |
| **ba(inst)** | **node** | Post-scheduling APackage, per instance/specialization in the demand-driven future. |
| **vseg(mod)** | **node** | Abstract Verilog body with symbolic child instantiation sites (§10). |
| Bluesim cxx | **node** (per module) | The staged-flow arc (staged-flow/3-codegen, 4-link-regen) makes per-module codegen real; enabled by schedule composition flowing through the boundary artifact. |
| BIR | two **nodes** | Already cache-seam shaped in trs: per-module-type segments composed per link. |
| link/compose | **node** (design) | All backends converge: per-module segment + design-level composition. |
| test verdicts | **node** | Terminal, tiny, the primary shared object for CI. |

Cross-cutting machinery: `resolve(name)` nodes (tracked path lookup —
negative dependencies made systematic, and the sound substrate for §9's
shadowing); flag partitioning per node kind; tool-version oracles; and
the **position rule** — positions may live inside impl (inlining errors
need them) but must never leak into iface, contracts, or generated-name
identity.

**Diagnostics are values.** Every node's result is (artifacts,
structured diagnostics — tag, span, rendered text); failures are
cacheable values, not absences; a cache hit replays its warnings (GHC's
lost-warnings lesson). The error-message test population becomes
assertions over cached diagnostics keyed on the stable T/G-tag
vocabulary.

**The fully-signed fast path.** A package whose exports are all
explicitly signed can publish iface from parsed + symtab with no
inference — importers unblock before typechecking starts.
Signature-completeness becomes an opt-in latency lever and a candidate
monorepo convention.

## 7. Contracts: precise and declared

Every `ba` has exactly one **precise** contract — the most-specific
boundary derivable from it. Parents elaborate against **declared**
(more general) contracts that many implementations satisfy:
substitutability and cache stability are the same property. Conformance
is its own checkable node — `precise(ba) ⊑ declared` — where the
implementation must be *at least as permissive* as declared (declaring
a conflict that the implementation lacks is safe; the reverse is
unsound).

**Today's gap.** The `.ba` almost contains the precise contract: six of
eight boundary inputs are present or derivable, but `veriPortProps` and
`true_ifc_ids` are computed and dropped (stored nowhere); the boundary
type is stored Module-monomorphized with provisos dropped; the schedule
is entangled with internal rule names. First code step: **make
`contract(ba)` a total pure projection** — persist the two fields plus
the source-form boundary type in the ABin; write the name-stripping
schedule projection. (Field semantics: `true_ifc_ids` = the always-ready
method set — literally a name→promise entry; `veriPortProps` = per-port
properties whose own source comment calls them "attributes for the
Cmoduleverilog (import-BVI)".)

**Enumeration principle.** The contract is what the monolithic flow
*recomputes and discards* at every boundary. That is why those fields
were homeless for twenty years, and the audit procedure for the
contract format: anything re-derived per session at a boundary belongs
in it.

**The ba connects, not conflates.** An implementation is precisely the
thing that connects a semantic contract to a physical realization, so
the `.ba` legitimately contains both layers *and the mapping between
them* — it is the **witness** that they cohere. The conflation sin
belongs to VModInfo-as-the-boundary-abstraction, not to the
implementation artifact. Consequences: for a derived pair, conformance
— including every sharing-class obligation of §10 — was *proved by the
child's own scheduler during elaboration*; the ba records that proof,
so no checker re-derives it. Checkers are needed only where the witness
is absent: asserted realizations (BVI) and re-binding a realization to
a semantic contract other than the one it was elaborated against.

## 8. Two maps, three imports, one action

- **contract : Name → Promise** — API material; the only thing in a
  parent's elaboration key.
- **binding : Name → Implementation** — configuration material; per
  design, per mode, per *test*; a build input and therefore a cache-key
  input.

Precedents: VHDL's entity/architecture/**configuration**; GHC Backpack
(instantiation identity must enter artifact identity — unit-ids ≡ cache
keys; signature matching ≡ conformance).

Importing a `.bo`, importing a `.ba`, and `import "BVI"` are one action
— *elaborate against a contract* — differing in provenance: source
semantics (may inline), promise semantics (implementation linked, never
re-elaborated), and hand-written promises over a foreign implementation.
Elaboration already treats synthesize boundaries as opaque
instantiations; the contract makes the re-derived boundary durable.
Discovery needs no manifests: link already walks the `.ba` hierarchy by
module name on the search path; `resolve()` nodes make that tracked.
Manifests appear only at static-graph boundaries (§4 pattern D), and
are generated.

The binding map is the formal home of mocks (alternate binding),
BVI-vs-model (two implementations, one contract), and combined-vs-
separate mode (separate binds a `ba` and assumes the contract; combined
binds the impl with permission to inline through — extra knowledge that
may change optimization, never observable behavior; the compatibility
test is exactly that differential).

## 9. Contracts as values

Contracts are ordinary elaboration-time values. Consequences:

- **Reunification.** Contracts live in packages and ride the existing
  interface/object machinery; there is only ever the ordinary package
  import, and what varies is which *values* arrive. Hand-written
  contract libraries are just packages.
- **The degenerate-contract observation.** A contract binds a name to
  (type, promises); a package signature already binds names to types.
  An iface entry is a contract with an empty promise set. One data
  model spans the spectrum (node kinds and keys stay distinct by
  consumer).
- **The primitive exists twice in embryo.** `fromContract :: Contract a
  → Module a` is GenWrap's from-wrapper (over derived boundaries) and
  what `import "BVI"` elaborates to (over asserted ones). Reifying the
  input unifies the code paths. The type must absorb module arguments
  and Clock/Reset (which cannot ride Bits-based wrapping), so the
  contract value carries the full boundary and the primitive dispatches
  Wrap-style.
- **Generated contracts and shadowing.** Elaboration's output splits
  into implementations (`.ba`) and *contracts provided* (a generated
  contract package — working suffix `.bc` — plausibly exporting
  `mkFoo = fromContract contract_mkFoo` itself). The standard flow:
  import the package as always, with some names **shadowed by the
  `.bc`** — the binding map materialized as *resolver configuration*.
  Combined vs separate mode = two resolver configurations over
  byte-identical sources. Shadowing must be a tracked, keyed resolution
  decision (the `resolve()` node with the mode in its key), never a
  path accident.
- **The algebra.** Weakening (forgetting promises — always sound; it is
  the subtyping coercion), projection onto subinterfaces, composition,
  and parameterization: a polymorphic module family's contract is a
  function from types/parameters to contracts, and a specialization
  request is its application at a concrete point. Documentation
  generators are folds over contract values. **The canonical
  serialization of a contract value is the cache key of the
  specialization that provides it** — the language and the build graph
  share one identity notion.
- **Provenance.** Users can construct contract values, asserting
  promises no implementation keeps (as `import "BVI"` always allowed).
  Derived and asserted contracts share the type but must not be
  confusable: a small trust lattice — derived / asserted / validated —
  where weakening, projection, and renaming preserve "derived";
  construction and strengthening yield "asserted"; conformance or
  differential validation upgrades asserted toward validated.

### Import strata

Finer dependencies and better caching demand that importing a package's
*contracts* and importing its *implementations* be distinguishable —
demand-tracking alone gives the exact dependency cone, but not a
*guarantee*. The layout that avoids both "two same-named packages with
shadowing magic" and "a differently-named generated package that breaks
mode-neutral sources": **strata as sibling sub-artifacts of one package
identity**, which the iface/impl split already established. A package
Foo has stratum artifacts `Foo.iface`, `Foo.impl`, `Foo.contracts`
(the generated contract stratum, produced post-elaboration and attached
to the same identity), each an independent node with its own key.

Import syntax then selects strata:

- `import Foo` — resolver-merged (mode-sensitive): the tracked
  `resolve()` node, keyed by mode, decides whether names resolve to
  source-backed or contract-backed definitions. Keeps sources
  byte-identical across combined/separate — the property the
  differential compatibility test depends on. The "weird shadowing
  relationship" becomes a *defined stratum-merge policy* under the
  tracked resolver.
- `import contracts Foo` (spelling TBD) — bound to the promise stratum;
  provably never touches `Foo.impl`, so the importer's key excludes
  implementations *statically*, at typecheck, not merely dynamically.
  This is also the redaction-consumer form: it works when only the
  contract stratum ships.
- `import concrete Foo` (spelling TBD) — never shadowed; guarantees
  source semantics (inlining available) for consumers where combined
  behavior is the point.

Division of labor stands: **syntax declares the dependency stratum;
configuration selects implementations within it** — binding stays
configuration, and full source-level pinning of realizations stays out
of the language.

Precedents: GHC's `{-# SOURCE #-}` imports (hs-boot) are exactly
stratum-selecting import syntax with a two-artifact consistency check —
which maps onto this design's conformance node — and hs-boot's chronic
pain (hand-maintained boot files drifting) is solved here because the
contract stratum is *generated*, with hand-written contracts checked by
conformance. Backpack distinguishes signature-dependencies from
module-dependencies as differently-keyed edge types. OCaml's universal
compile-against-interface is the limiting design, unavailable here only
because impl-stratum consumption (cross-module inlining) is
elaboration-demand-driven — which is precisely why the contract-stratum
import's static exclusion guarantee is worth surface syntax.

Build consequences: an import edge is (package identity, stratum,
stratum-artifact hash); contract-stratum edges make parents immune to
child implementation churn at the typecheck key, not just the
elaboration key; the dependency scanner classifies stratum from syntax,
so stratum-typed import graphs — and the frozen-mode manifests of §4 —
are computable without running elaboration; and dynamic independence
still refines within the declared bound (exact cone ⊆ declared stratum,
checkable).

## 10. The semantic/physical split

Treating "the contract" as a VModInfo conflates two layers:

- **Semantic contract** (Bluespec-level): interface types, method-level
  scheduling relationships (the CF/SB/ME projection), clock and reset
  *domain* structure and crossing promises, always-ready/always-enabled
  promises, argument/result types. What a parent's **elaboration and
  scheduling** consume.
- **Physical realization** (RTL-level): the mapping of Bluespec
  entities to ports — names, widths, roles; argument-as-port vs
  parameter; clock/reset *port* bindings; port-sharing structure;
  protocol encoding. What **netlist composition** consumes.

The two homeless fields of §7 land one per layer — `true_ifc_ids`
semantic, `veriPortProps` physical — evidence the cut is natural. And
several existing attributes (`always_ready`/`always_enabled` port
elision, BVI port renaming) are physical-layer freedoms currently
entangled with the pragma/type surface.

**The value of the separation** is compiling abstractly and wiring
different implementation choices differently: a parent elaborated
against the semantic contract alone can be bound to realizations that
differ in port naming, bundling, sharing, and encoding — without
re-elaboration. Two instances of one semantic child can bind to
*different* realizations in one design (a netlist and a model,
in-situ A/B).

**The residual coupling** — the one place physical facts cast a
semantic shadow — is port sharing: when two methods share output (or
argument) ports, simultaneous use must be impossible or provably
value-equal. Formalized, it stops being a leak: each realization
publishes its **sharing classes**, each with a justification obligation
— *disjoint use* (entailed by the semantic contract's ME/CF structure)
or *value equality*. Realization conformance = every sharing class's
obligation is entailed by the semantic contract it claims to realize. A
realization with more sharing needs a stronger semantic contract; the
check is per (realization, semantic-contract) pair — a verdict node.
Parents never consume ports; they see only any induced scheduling
constraints, which by construction already live in the semantic layer.

**How far does protocol freedom extend?** The crisp line: **same-cycle
(combinationally bisimilar) re-encodings are physical freedom** —
renaming, bundling, polarity, sharing, RDY/EN elision, argument
encoding. **Latency-changing protocols are not**: Bluespec's method
semantics are per-cycle, so a registered or credit-based handshake
changes observable behavior and therefore belongs to a *different
semantic contract*. Extending flexibility across cycles requires a
weaker, latency-insensitive semantic contract class (the Carloni line)
— a real future direction, but a semantic-layer extension, not a
realization choice.

**The Verilog consequence — different but right.** Today parent Verilog
codegen bakes child port wiring into the parent's `.v` using VModInfo
known at parent-compile. Under the split, parent codegen emits
**vseg(mod)**: an abstract body with symbolic child instantiation sites
keyed by (child method, role); **vlink(design)** substitutes the bound
realizations' port maps at link. Verilog generation thus needs the
realizations (`.ba`s) of the things it uses at link time — exactly as
the Bluesim and trs flows already do. This completes the backend
symmetry: every backend is per-module abstract segment + link-time
composition against bound realizations (Bluesim cxx + link-regen; trs
birseg + birlink; Verilog vseg + vlink). Precedent already in-tree: the
link-time `.ba` walk (needs-timing analysis) and the staged-flow
"link-regen" rung. Cache consequences: vseg survives realization swaps
(and is *more* alpha-stable than today's `.v`, since child port drift
no longer touches it); only vlink recomposes. Compatibility: vlink can
still emit per-module `.v` files, and a sealed mode reproduces today's
bind-at-compile behavior.

Binding becomes two-stage: **elaboration-time** (name → semantic
contract) and **link-time** (semantic instance → realization). And
`import "BVI"` decomposes fully: an *asserted semantic contract* plus a
*foreign realization* (the port map — which always belonged to the
realization, not the contract).

### Clocks and resets under the split

The split's first concrete application inside the compiler: **the
(oscillator, gate) wire pair is a physical realization choice, and
today it is baked into elaboration.** `AClock` is literally
`{ aclock_osc :: AExpr, aclock_gate :: AExpr }` (ASyntax.hs:980), and
IExpand threads gate wires through the semantic evaluator
(`getClockGate` et al.) — physical plumbing inside the semantic phase.

Under the split:

- **Semantic clock** = domain identity plus *relationships*: this
  domain's edges are a subset of that domain's, controlled by an
  abstract gating condition G (itself a Bluespec-level semantic value);
  derivation and crossing promises. In bsc's per-cycle semantics,
  "gate off ⇒ nothing in the domain fires" is all a parent's
  elaboration and scheduling ever consume.
- **Physical realization** = how a domain's clock arrives at each
  boundary: a bare wire; an (osc, gate) pair; gate absorbed into an ICG
  cell (what ASIC flows actually do — bsc's CLK_GATE outputs are
  routinely unused there); or **enable-folding** — the gate rendered as
  a conjunct of the child's implicit conditions.
- **Nothing happens in elaboration.** IExpand stops threading gate
  wires; clocks become abstract domain references; all osc/gate
  materialization moves to the realization/link stage. A substantial
  simplification of a notorious complexity source.
- **Enable-folding is a boundary coercion, not a semantics.** It
  applies exactly when the gating signal is not deliverable at a module
  boundary (the bound realization has no gate input — the BVI case
  today). In the per-cycle semantic model it is *exact* — identical
  firing sets — while differing only in properties outside the model
  (power, physical clock activity, clock-tree structure). A
  transformation invisible to the semantic layer and meaningful only
  physically is the *definition* of a realization choice: the cleanest
  possible demonstration that the layer boundary is drawn correctly.
  Legality: bsc-generated children are always enable-suppressible by
  construction (every firing is EN-guarded); foreign realizations only
  if their asserted contract says so. The reverse coercion (ungated
  parent, gate-expecting child) is tying the gate true.
- Bluesim and trs never wanted gate *wires* — they want the semantic
  relationship (edge suppression) and today reverse-engineer it from
  the physical encoding. Under the split they consume the semantic
  layer directly — the `veriPortProps` XXX comment's wish, granted for
  clocks too.

Reset is symmetric (sync/async assertion style, polarity, and port
encoding are realization; domain membership and assertion semantics are
semantic) — and the recent InitialReset fix is the miniature precedent:
moving its hold register to a polarity-independent encoding was exactly
a physical-encoding-leaked-into-semantics repair.

## 11. Migration order

1. **External Shake driver** over today's artifacts (§3) — ships
   parallelism; touches nothing in bsc.
2. **Make `contract(ba)` total** (§7) — ABin additions + projections;
   coordinate with in-flight format-tag bumps.
3. **iface/impl split of the `.bo`** (§6) — ships cutoff and the staged
   flow; the CtxRed-retirement raw-telescope serialization is the iface
   content.
4. **Semantic/physical factoring of the boundary** (§10) — VModInfo
   splits into SemContract + Realization; vseg/vlink for Verilog,
   completing backend symmetry.
5. **Contracts as values + generated `.bc` + resolver shadowing** (§9).
6. **Demand-driven specialization** on the rails 1–5 laid (§4 hooks;
   contract-value hashes as node keys).
7. **Per-definition impl demand** only if profiling justifies.

## 12. Open questions

- Suffix and packaging of the generated contract artifact (`.bc`?) and
  whether it is literally a generated package.
- `fromContract` typing: module arguments, Clock/Reset, parameter
  encoding; the Wrap-style dispatch mechanism.
- The provenance mechanism (type-level, value-level, or
  artifact-metadata) for derived/asserted/validated.
- The sharing-class justification checker: entailment against the
  semantic schedule projection; value-equality obligations.
- Whether/when to introduce latency-insensitive semantic contracts.
- The flag-partitioning table (which of bsc's ~135 flags key which node
  kinds).
- Method-protocol taxonomy: the precise definition of "combinationally
  bisimilar re-encoding".
- Whether `vlink` should also perform cross-boundary flattening on
  request (recovering combined-mode optimization within the split
  architecture).
- The surface typing of gating conditions once gates leave elaboration
  (today's gate-as-wire surface operations need semantic-condition
  counterparts).
- An ICG-cell realization library and its conformance story
  (glitch-safety obligations live entirely in the physical layer).
- Whether enable-folding should be expressible as a user-visible
  realization annotation (per boundary) rather than only an automatic
  fallback.
- Import-strata surface spelling; the exact stratum-merge policy for
  plain `import`; whether `import concrete` is needed or an attractive
  nuisance; whether export lists also want stratum annotations.

## 13. Relation to the post-GenWrap design (July 2026)

`doc/design/post-genwrap-compiler.md` on nanavati branch
`claude/model-rqj7c1` (the "Post GenWrap bsc step 2" session, 2026-07;
4,092 lines, with an implementation lane: `BoundaryDesc.hs`,
`GenBoundary.hs`, `ContractCheck.hs`, the as-built increments of its
§12–§13, and `src/trs/docs/BOUNDARY-CONTRACT.md`) is the direct ancestor
of §§7–10 here, worked out at the compiler-internal level. This RFC and
that document interlock: it supplies the in-compiler mechanism; this one
supplies the build-graph organization, the testsuite/verdict layer, the
clock refinement, and import strata. The correspondence, with its
vocabulary **adopted** where sharper:

| This RFC | Post-GenWrap design |
|---|---|
| Semantic contract | **IfcContract** (§3.1.1/A15): a *type-indexed value* — method→domain in formal domain variables, resets, scheduling matrix, paths; travels wherever the type travels, attaches even to interface *arguments* with no module behind them (its §3.5) |
| Physical realization | **BoundaryBinding**: names, multiplicity, presence, kind, per-port declared surface type (A16), dressing — per (implementation, specialization key), the *output of library rendering code* |
| "The ba connects, not conflates" | Its altitude summary, verbatim in spirit: VModInfo is the **materialized join**, so `avi_vmi` and everything downstream stay byte-for-byte |
| Sharing classes + justification obligations | **Licenses** (adopted): *every collapse in the mapping needs a license from the semantic half* — RDY drop ⇐ always_ready; port sharing ⇐ declared conflicting (#658's soundness condition: a scheduling fact licensing a port fact); port drop ⇐ zero width at this key; the one genuine impossibility is a kind mismatch in the dynamic direction |
| Derived / asserted + conformance | **fill / verify**: one function, two modes; equality where the contract is total (ports), refinement where it is a bound (schedule, paths); contracts validated at construction |
| Contract-value hash as specialization key | §4.2–4.3, sharper: key = (module Id, type instantiation, **resolved dictionary-tree hashes**) computed in the evaluator — dictionaries hashed because bsc classes are not coherent; incoherence becomes *observable*; the key recorded in the parent's ba; "dictionaries are nameable, hashable values resolved before elaboration" |
| Demand-driven ba(inst) | §4.4: nested, memoized, **reentrant genModule** with a demand stack (cycle detection with a blame chain; decreasing-measure self-demand terminates); precedent: AAddSchedAssumps already nests runTI→iExpand→aConv mid-compile |
| Frozen/manifest mode; pattern D | §4.5, pre-invented: a machine-readable manifest of demanded specializations per compile, plus a mode where a specialization artifact is produced by a *separate build-system-invoked command from the recorded key* (keys are reconstructible — pure functions of boundary-crossing information); atomic publish; determinism as a CI invariant (bit-identical double-compile); the #290 preprocessor-blind staleness fix |
| Mocks fall out of binding | **stubOf : IfcContract → Impl a** — stubs *generated from the contract* (all-CF refines anything; drift impossible); every synthesized module stubbable, subtree stubbing with no re-elaboration |
| Adapter between realizations | **A21/A23/A24**: adapters are arbitrary functions `toB ∘ fromA` elaborated by the evaluator (data plane), with RDY/EN/clock/reset staying structural under the licenses (control plane); the round-trip law `from ∘ to = id`; bindings carry **rendering witnesses** — name+hash references to the rendering dictionary, never bodies |
| The split's governing principle | **A20** (adopted): *design for type and schedule/clocking compatibility, never wire compatibility — port names stop being API*; the boundary ABI is (interface type, IfcContract); "the same inversion typed languages made when the compiler took ownership of the calling convention" |

**Link-time replacement arrives for free.** In the July design,
link-time module replacement existed as a *feature*: `mkOneOf ::
IfcContract → [(String, Impl a)] → Module a` — a static, literal
candidate list, all N bodies elaborated at the module's own compile
(the artifact-ownership wall), the parent scheduling against the
declared contract, and link merely *selecting* by name; open-world,
link-time-discovered substitution was a stated restriction. In this
RFC's formulation it is the default path: the parent's vseg holds
method-level wires with symbolic instantiation sites and never bakes a
binding, vlink applies whichever bound realization's binding at link,
and the parent schedules against the semantic contract — so replacing a
module at link with *any* conforming implementation requires no
combinator, no pre-enumeration, and no parent recompilation. The July
restriction survives in exactly one refined form: **witnessed
(arbitrary-function) renderings need adapter elaboration.** Free
substitution therefore covers binding-compatible and structural
(witness-less) realizations outright; a witnessed realization needs
either a link-time re-render step — possible in this RFC's world
precisely because A24 witnesses are name+hash references vlink can
rehydrate and elaborate — or falls back to mkOneOf-style
pre-enumeration. mkOneOf itself demotes to sugar: still the source-level
way to declare a variant set (and stubOf's home), no longer the only
door to substitution.

**One deliberate tension to resolve.** The July design's load-bearing
invariant is conservatism: backends and parents read only `avi_vmi`
(the join), so *nothing downstream changes*. This RFC's §10 endgame
(vseg/vlink) deliberately revises that invariant to complete backend
symmetry. Reconciliation: the invariant governs every rung up to and
including contracts-as-values; vseg/vlink is a later rung that replaces
the join-consumption *consciously*, with the sealed mode preserving the
old path. The July doc's ClockContract (osc/gate port names in the
record) likewise predates §10's clock refinement: under this RFC those
fields move from IfcContract to BoundaryBinding.

## 14. Schedule polymorphism

Unifying the contract lattice with the polymorphic-scheduling view:
schedules have type-like relationships, and the machinery of §§7–9
already contains everything needed to treat them that way.

**The lattice.** Per method pair, the scheduling relations order by
permissiveness: `CF ⊒ SB(a<b), SB(b<a) ⊒ C` — a diamond, with the two
orderings incomparable siblings. Matrix-level order is pointwise. Then:

- The **precise** contract's schedule is the *principal* schedule —
  bsc's scheduler already computes it (principal-type inference, already
  implemented).
- A **declared** schedule is an *ascription*, checked by subsumption —
  the July design's verify mode is literally the subsumption check.
- **Weakening** is upcast; **conformance ⊑ is the subtyping relation.**
- The **subsumption lemma** (the soundness core, worth stating once): a
  parent correct against schedule `s` remains correct against any
  `s' ⊒ s`. Substitutability is monotone in the lattice. The parent's
  *optimal* schedule may improve under a more permissive child — but
  that is a recompile-for-optimization choice, never a correctness one.
  (This is combined-vs-separate mode restated in lattice vocabulary:
  elaborating against the precise schedule is combined-mode
  optimization; against the declared bound is separate-mode stability.)

**Schedule variables.** A polymorphic contract quantifies over schedule
variables with lattice bounds, exactly as it quantifies over types:
`fifoFamily :: SchedPoint → IfcContract (FIFOF t)` is an ordinary
contract-family function in the §9 algebra, and schedule parameters
join type variables and dictionary hashes in the quantified telescope —
including, naturally, in specialization keys, and (a pleasing tie-in)
as *specified binders* in the visible-type-application sense:
`mkFIFO @Pipeline` selects a family point. Two inference directions
complete the picture:

- **Principal offer**: an implementation's precise schedule (exists
  today).
- **Principal requirement**: the *weakest* child schedule under which a
  parent's rules still schedule — inferable from the parent's own uses
  (does any rule need enq and deq in one cycle, and in which
  data-dependence order?). A schedule-polymorphic parent compiles to a
  constraint (`requires s ⊒ needs`), and binding is the constraint
  check. The precedent is effect systems: schedules *are* effects, this
  is row/effect polymorphism with principal effect inference, and the
  monotonicity lemma is what makes bounded quantification compositional.

**The canonical family.** BypassFIFO and PipelineFIFO are concrete
realizations of one polymorphic implementation at the two incomparable
SB points; the *blocking* FIFO (enq or deq per cycle, never both) is
their **meet** — the greatest promise both refine — and a dual-ported
CF FIFO would be their **join**. A parent declaring only the blocking
contract works with all of them; a parent needing same-cycle enq+deq
must declare which ordering, and *which* is exactly the semantic
difference between pipeline and bypass — the lattice makes the folklore
precise. One source can generate the whole family (the conditional
bypass/pipeline mux idiom already hand-rolls this), with the schedule
parameter as a specialization-key component.

### 14.b Schedules as values

Contracts-as-values implies schedules-as-values: a contract *contains*
a scheduling matrix, so the schedule component is already a value; the
completion is letting it exist outside the contract — as a module
parameter and an ascription — exactly the position Clock and Reset
already occupy. The symmetry is worth stating as the design's slogan:
**a module's entire control surface — clocking, reset, scheduling —
becomes first-class semantic values with deferred realization** (data
methods always were values: the interface). Clocks: semantic domain
value, realized as wires or gates (§10). Schedules: semantic ordering
value, realized as will-fire logic.

**The precedent is Kôika** (Bourgeat, Pit-Claudel, Chlipala, Arvind —
"The Essence of Bluespec", PLDI 2020): rules plus an *explicit,
user-provided schedule* as a syntactic object, one-rule-at-a-time
semantics proved as a theorem *for every schedule*, dynamic aborts when
a rule's effects would violate the ordering, and a verified compiler to
RTL. Its headline capability is exactly the claim here: performance
tuning by changing the schedule value while rules stay untouched —
schedule polymorphism as the design method, not a pragma bag.

The bsc mapping:

- **The pragma surface demotes to constructors.** `descending_urgency`,
  `execution_order`, `preempts`, `mutually_exclusive`, `conflict_free`
  become constructors of a typed Schedule value — one object, validated
  at construction (the July §3.3 demotion, applied intra-module), with
  bsc's real distinction between urgency (who wins the resource) and
  execution order (sequential position) preserved in the type rather
  than blurred across attributes.
- **The fill/verify dial extends into the module.** No schedule value =
  today's full inference. A *partial* value = today's pragmas, made
  principled: constraints the scheduler completes (principal
  completion). A *total* value = Kôika mode: cycle-accurate control,
  verified legal rather than inferred — the principled exit for the
  "fighting the scheduler" class of user pain.
- **The forwarding semantics already exists.** Kôika's expressive power
  rests on EHRs (Rosenband's Ephemeral History Registers) — and bsc
  *has* them: `mkCReg` is the EHR. What bsc lacks is only the schedule
  surface, not the register semantics that realizes aggressive orders.
  The gap is smaller than it looks.
- **Dynamic scheduling already shipped schedule values.** The
  `-sched-dynamic` work's SchedAlt machinery — guard-selected schedule
  alternatives in the composition artifact, chosen per clock edge — is
  literally *runtime-selected schedule values*. The static story
  completes the same move: a schedule value with guarded alternatives
  is one more constructor, and the dynamic engine becomes an evaluation
  strategy over schedule values.
- **Honest v1 scope.** The value type ranges over the constraint
  language plus totality; SAT-derived facts (ME proofs, disjointness)
  stay inferred and are *recorded into* values, not written by hand.
  And bsc-realizable orders are the v1 codomain — Kôika-arbitrary
  orders are realizable exactly where CReg-style forwarding is in play,
  which becomes a checkable legality condition rather than a semantic
  extension.

What it buys, in this RFC's terms: schedule polymorphism becomes
ordinary value parameterization (`mkFIFO sched` — the §14 family is an
argument, not a naming convention); the provenance lattice covers
schedules (asserted BVI schedule annotations, derived inferred ones,
validated verified ones); documentation and why-didn't-this-fire
tooling fold over schedule values as they fold over contracts; and the
differential-testing frame sharpens — two implementations of one
declared contract differ, within the bound, exactly by their schedule
values.

## 15. The pre-.bo eager layer: giving up early inlining

The question, precisely: bsc does *some elaboration-style inlining in
advance*, at package-compile time, baked into the `.bo` — a structural
echo of CtxRed. What would giving it up gain, and do we know what it
costs? **The gains are the identity properties this whole RFC is built
on; the cost is unmeasured, decomposable, and the instrumentation
half-exists.**

**Anatomy of the layer** (post-typecheck, pre-`.bo`-write, bsc.hs
~540–600): `LiftDicts` lifts dictionary expressions to top-level CAF
definitions carrying evidence identities; `fixupDefs` **redirects local
lifted dictionaries to evidence-equal imported ones** (first verified
candidate in import order — a cross-package dependence of my `.bo`
bytes on the imports' lifted-dictionary *inventory and order*);
`iSimpDicts` expands lifted dictionary CAFs to manifest tuple form
"so ISimplify can inline them efficiently"; and `iSimplify` — run
twice, with an XXX — beta-reduces, inlines through definition heads,
and simplifies, with a TODO list written "from looking at .bo". The
layer's purpose is CtxRed's purpose one phase later: make dictionaries
cheap, eagerly, package-wide, with the output baked into the durable
artifact.

**What "give up" should mean — the CtxRed-retirement principle applies
verbatim** (*the written form is identity; solved facts are a cache*):
the `.bo` impl stratum stores the **raw** post-typecheck/IConv
definitions (identity), and the simplified/deduplicated forms become a
**derived node** — `simp(pkg)`, keyed on (impl, simplifier version) —
with dictionary deduplication moving to the elaboration-time evidence
cache the CtxRed retirement's P2 already plans. Not lost work: moved
out of the identity artifact into cache, where heuristic drift is
harmless. The in-tree precedent for the mechanics is sitting in the
IPackage record itself: the ATF cache is already a per-package annex.

**Gains, now precise:**

- **True iface-keyed `.bo` production.** Today a dictionary added
  *inside* an import can change my `.bo` bytes (the fixupDefs redirect
  target shifts with inventory/import order) with nothing semantic
  changed for me. Raw-identity impl kills that: `.bo` = f(source,
  import ifaces).
- **Canonicality.** Simplifier-heuristic drift stops churning `.bo`s —
  the alpha/cache-stability theme of this RFC, at the artifact that
  matters most. The double-run XXX is this smell made visible.
- **Clean per-definition impl nodes** (definitions not pre-fused into
  each other), and faster package compiles on the critical path.
- **Better dedup, lazily**: fixupDefs dedups against direct imports in
  import order; an evidence-keyed elaboration-time cache dedups
  globally and order-independently.

**Costs, decomposed (the honest unknown):**

1. *Amortization loss*: simplification once per definition per
   consuming design, instead of once per definition — for Prelude-class
   definitions used by everything, real. Bounded by the fact that
   elaboration re-simplifies whatever it inlines anyway.
2. *Evaluator pathologies on raw forms* — the scary tail: unsimplified
   dictionary spines at every use site are exactly the class of
   superlinear evaluator blowups the primitive-fixes work documented.
   Any experiment must include the perf-stress designs, not
   microbenchmarks.
3. *`.bo` size and load time* (raw bodies are bigger). Modest;
   measurable.
4. *Elaboration-time dictionary duplication*: fixupDefs' redirects also
   mean evidence-equal dictionaries elaborate once because they are one
   definition; the lazy replacement must catch this in the evidence
   cache or pay per-name re-elaboration.

**The experiment** (instrumentation half-exists: `-trace-drop-dicts`
and `-trace-simp-dicts` are already in the tree): a flag skipping
iSimpDicts + iSimplify (and optionally fixupDefs redirects) at
`.bo`-write; compile the library, the testsuite corpus, and the
perf-stress designs both ways; measure package-compile time, `.bo`
sizes, full-design elaboration time and memory, and `.bo` byte-stability
across simplifier tweaks; use the traces to size redirect and
simplification hit rates. The middle target is the likely winner and is
this RFC's shape anyway: keep the eager work but store it as the
derived `simp(pkg)` node/annex beside a raw impl — identity properties
and amortization at once, at the cost of carrying both forms.

### 15.b The adjacent question: auto-boundary for cross-package modules

(Distinct from the above — the question first answered in this
section's earlier draft; retained because it is real and complements
it.) Function-level cross-module inlining at *elaboration* stays:
elaboration is inlining; hardware has no calls. The elaboration-level
candidate is **auto-boundary for cross-package module instantiation**
(compile parents against contracts, never bodies). The `.bo`-level gain
is already captured by the iface/impl split; auto-boundary's additional
gains are elaboration-level: per-package elaboration artifacts and
reuse, smaller elaboration closures (the 20–30 GB elaborations shrink
when children are boundaries), redaction by default, and the contract
economy applying to every cross-package edge.

**Cost classes**, with recoverability noted:

1. *Constant/parameter propagation into children* — **recoverable**:
   under specialization-first, a constant argument becomes a key
   component; propagation is restored per key, at artifact-count cost.
2. *Dead-method/port elimination* — partially recoverable (a used-method
   set could join the key; artifact explosion is the tradeoff).
3. *Condition specialization of method calls* — lost at boundaries.
4. *Cross-boundary logic sharing / CSE* — genuinely lost to bsc;
   largely recovered downstream by synthesis flattening for ASIC QoR,
   not for simulation cost.
5. *Parent–child rule composition* (urgency across the boundary; intra-
   cycle interleaving of child internal rules with parent rules) —
   genuinely lost; exactly what `(* synthesize *)` users already accept
   today.
6. *Schedule conservatism* — only under **declared** contracts; fill
   mode gives parents the precise method matrix, so this cost is a
   choice per edge (the subsumption tradeoff of §14), not a tax.
7. *Expressiveness subset*: modules with function-typed or non-Bits
   arguments cannot cross a boundary (closures are not serializable
   keys — the July §4.3 line); polymorphic uses need specialization-
   first as a prerequisite. These stay inline; the question is what
   fraction of cross-package edges they are.

**The experiment** (cheap with this session's tooling): an
`-auto-boundary-cross-package` mode over the legal subset, run over the
testsuite corpus and a production fleet, measuring — the legality
census (what fraction of cross-package instantiations can boundary at
all, and why not); compile time and peak RSS per package and end to
end; generated-Verilog delta via the alpha-equivalence comparator plus
gate counts after a synthesis pass on a sample; Bluesim/verilator
runtime delta; and schedule diffs (any parent whose behavior-relevant
schedule degraded). Two priors worth recording: production fleets
already compile with heavy `(* synthesize *)` discipline, so the
boundary-cost question is really about *library-heavy, inlining-
dependent* code; and the middle path already exists in this RFC —
import strata let consumers opt into signature-only per edge, so the
default can follow the measurements rather than precede them.

## References

- Query-based compiler architectures: rust-analyzer/salsa; rustc
  red-green; Rock. Build systems: "Build Systems à la Carte"; Shake;
  GHC Hadrian (Shake at scale, including its stabilization cost).
- Module systems: ML signatures/structures; VHDL
  entity/architecture/configuration; GHC Backpack.
- In-tree precedents: staged-flow branch arc (per-module Bluesim
  codegen, link-regen); trs BIR segment/link split; the link-time `.ba`
  walk; GenWrap's from-wrapper and the `veriPortProps` import-BVI
  comment; `Depend` as the exposed scanner.
