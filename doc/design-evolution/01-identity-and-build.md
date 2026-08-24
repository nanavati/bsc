# 01 — Identity, Artifacts, and the Build

How bsc's outputs, caches, tests, and builds converge on one identity
discipline. Companion to RFC-bsc-artifact-graph.md, which governs on
mechanism; this document states the destination and the reasons.

**Status:** v2.0 — 2026-08-24 (Claude). Design only; sequencing,
status, and provenance live in the KB lanes and the meeting-notes
digest, outside this set.

## 1. The design in one paragraph

Decompose bsc along **cache seams, not process seams**: a vocabulary
of typed, content-addressed artifact nodes (parsed, iface, impl,
semcontract, realization, ba, vseg, BIR segments, verdicts) with pure
derivations between them, orchestrated by a build engine, with process
boundaries demoted to per-node deployment choices. `bsc -u` becomes
the engine; the node vocabulary becomes the public API; schema tags
key both caches and consumers; the testsuite consumes the same graph.
The same decomposition surfaces externally as **phase executables**:
one executable per compile phase per backend — elaboration+scheduling
(source → interface/implementation artifacts), per-backend codegen,
per-backend link — so configuration cannot leak across phase contexts,
flags largely leave the persisted artifacts, and a legacy `bsc`
survives as a wrapper. A phase boundary deserves a process seam
exactly where its artifact earns caching, parallelism, inspection, or
a second consumer — the same rule that shapes the trs porcelain
(05 §1). Use-model requirement (07): the whole graph must be
containable by an outer static, hermetic build system with remote
caching — via tree artifacts, persistent workers, a
remote-execution-backed share, and frozen specialization manifests —
designed in from the start, not retrofitted.

## 2. The identity layer: format registry and transitive manifest

Nine independent lanes each demanded the same missing object; it is
one artifact family, not ten features (RESOLUTION — the design's
root):

- **One registry of format tags** (.bo, .ba, BIR, snapshots, plans,
  AOT layouts, callback ABIs) with rules for compatible vs breaking
  changes; readers reject unknown semantic fields (never
  skip-and-run); every serializer change goes through the registry.
  *Why:* every composition failure found by the cross-lane audit was
  an identity failure — schema drift a reader cannot detect is a
  silent semantic miscompile.
- **One transitive manifest schema** carrying five identities —
  decoder/schema revision; producer/toolchain; public semantic
  interface; implementation content; full action key — attached to
  every durable artifact and validated by every loader. Bindings
  (implementation selections, tiers, tool pins, FFI transports,
  X-policy vectors, capability profiles) live here.
- **Contract files are this manifest seen from the build side**: the
  inter-phase dependency descriptions of the phase-executable split
  and the artifact graph's manifests must be one specified artifact
  family, not two (RESOLUTION). A contract file can also be a
  *checking* surface — carrying expected scheduling and interface
  promises that the compiler validates rather than infers — which is
  T1 applied to the build boundary. A designed consequence worth
  exploiting: after elaboration a module's import set *shrinks*
  (consumers lose dependencies only the source needed), a caching
  lever the manifest layer makes expressible.
- **Fail-closed doctrine**: strict modes reject every fallback path;
  unclassified = non-cacheable; unknown = refuse; artifact identity is
  verified by digest before execution — a launcher is not an immutable
  artifact.

## 3. Interning, serialization, and the session architecture

FACT (measured; rationale for the design): hash-consing with cached
structural metadata pays for itself only under discipline — WHNF-only
deep-forcing at intern time, cached free-variable sets with
substitution pruning, structural fast-path bits that are architectural
rather than heuristic, content hashing with rank-first comparison.
The serialization strategy is **intern what you save, exempt what you
unify**: serialize the reachable, walk-ordered projection; derive the
tree-shaped residue; phase-index the type representation (Trees That
Grow) so "vanishes after this phase" is a compile error, not a
comment.

RESOLUTION — the **session architecture**. Process-global state moves
into an action-scoped context: one CompilationSession/QueryContext
owns the interner arena, the frozen rule/instance snapshot, and every
unique-keyed memo, with three declared lifetimes — (i) node-local
structural metadata (valid forever on immutable nodes), (ii)
out-of-node structural acceleration (valid per arena generation),
(iii) environment-dependent results (valid per semantic snapshot). No
memo outlives its environment or its interner generation; intern ids
never enter durable identity (run-local hashes are *comparison
fingerprints*, firewalled from content addresses). *Why:* four
independent consumers — in-process parallelism, the LSP worker, bluehs
persistence, constructor-time ATF folding — need exactly this and
nothing weaker; CLI-lifetime globals become correctness bugs the
moment any consumer outlives one compilation.

## 4. Identity vs cache: the definition-cache design

The organizing principle: **the written form is identity; solved facts
are a cache.** Durable artifacts store declared/raw forms; everything
solved — simplified definitions, dictionary specializations, ATF
ground reductions, derived contexts — is a demand-populated,
content-keyed cache entry that may be discarded but can never change
meaning. *Why:* an eager pre-persistence simplification layer makes an
artifact's bytes depend on its imports' private inventories, breaking
interface-keyed identity; eagerness returns as cache-warming policy,
never as identity semantics. The ATF cache, the definition cache, and
the evidence cache are three instances of one mechanism. Interface
self-containment is the correct layer for build-system recompilation
cutoff as well: declared-inputs pruning, direct-deps-only interfaces,
and the iface/impl split are the same design ascending in ambition —
with the standing caution that silent staleness is worse than slow
rebuilds, so every cutoff mechanism carries adversarial
interface-preserving tests.

## 5. Tests as graph nodes

Verdicts are first-class cached artifacts, and cacheability is
**earned by declaration**: hermetic / environment-scoped /
non-cacheable classes; unclassified = non-cacheable; deterministic
failures cache, infrastructure failures never do ("retry, don't
replay"). A cached PASS is a soundness claim, not an optimization —
so the share itself is audited, and gate ladders are graph
dependencies (a perf result against a red semantic gate is
unreportable by construction). Capability visibility is part of
verdict identity: an unavailable capability reads as *not covered*,
never as a green skip; bounded analyses export per-obligation
completeness so "no warning" is never consumed as "proved". Two hard
requirements from the external use model (07): test authors never
write Haskell, and the orchestrator never links the compiler under
test. The verdict-node design assumes the graph engine; that premise
is part of the destination, not just the plan (08).

## 6. Determinism as a designed property

Every artifact is a bit-deterministic function of declared inputs —
from the compiler's own build (rule-selection tie-breaks made total;
build-twice bit-identity as an invariant) to fleet-scale generated
Verilog (byte-stable output as the release currency of the static
use model, 07). Where a toolchain component cannot be made
deterministic by construction, determinism is established by seal and
the nondeterminism source is named. Methodology laws that ride the
design: every load-bearing number needs a raw artifact behind it;
profiling exemptions are declared or the profile fabricates cost;
negative results are recorded so they are not re-proposed.

## 7. Pointers

Mechanism: RFC-bsc-artifact-graph.md (driver, ladder, nodes,
interning, serialization, tests, containment). The identity layer's
demands originate across the coherence, ATF, interning, trs,
port-properties, BVI, verilator, and LSP lanes — indexed in the KB.
Open design decisions: 08.

## 8. RESOLUTIONS and OPEN questions

- RESOLUTION: the format registry + transitive manifest is the
  design's root artifact; contract files and manifests are one family.
- RESOLUTION: the session architecture is built once, for all four
  consumers; it is the acceptance condition for any persistent memo.
- RESOLUTION: definition-cache "dominance" is a measured hypothesis,
  not an axiom — the cache design stands on identity grounds alone.
- OPEN: the manifest's solver-identity and resource-policy field set
  (04 §4's ceiling; 08).
- OPEN: the clean-suite definition — zero unexpected verdicts with
  capability-visible coverage as the acceptance bar (08).
