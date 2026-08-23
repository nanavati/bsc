# RFC: The bsc Artifact Graph

Cache-seam decomposition, contracts, and the build.

**Status:** Draft v0.1 — strawman distilled from a design discussion
(Ravi Nanavati with Claude), 2026-08-23. Not proposed upstream; the
sections stand independently and are separable into individual proposals.

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
