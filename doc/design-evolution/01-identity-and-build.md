# 01 — Identity, Artifacts, and the Build

How bsc's outputs, caches, tests, and builds converge on one identity
discipline. Companion to RFC-bsc-artifact-graph.md (v0.21), which
governs on mechanism; this document adds the cross-lane resolutions
and the workstreams the reviews demand.

**Status:** v1.0 — 2026-08-24 (Claude, holistic review). Labels: FACT /
DECISION / PROPOSAL / RESOLUTION / NEEDS-RAVI.

## 1. The program in one paragraph

Decompose bsc along **cache seams, not process seams**: a vocabulary of
typed, content-addressed artifact nodes (parsed, iface, impl,
semcontract, realization, ba, vseg, BIR segments, verdicts) with pure
derivations between them, orchestrated by Shake, with process
boundaries demoted to per-node deployment choices. `bsc -u` becomes the
engine (the parallelism ladder: sidecar → internalized → stage-level →
node-level); the node vocabulary becomes the public API; schema tags
key both caches and consumers; the testsuite follows the engine once it
lands. A static, hermetic outer build system contains the same graph
via tree artifacts, persistent workers, a remote-execution-backed
share, and frozen specialization manifests (the containment posture;
the deployed instance is in 07).

FACT (2026-08-21 sync; 10 §1): upstream adopted the **3-phase compile
split into modular executables** with **contract files** for dependency
management and cache efficiency, plus Cabal for native build tasks. The
smaller-tools direction and this program are the same design seen from
two sides: a phase boundary is worth a process seam exactly where its
artifact earns caching, parallelism, or a second consumer — the trs
porcelain rule (05 §1.4) applied to bsc itself. RESOLUTION: the 3-phase
proposal's contract files and this document's transitive manifests must
be specified as one artifact family — a contract file is the manifest
of an inter-phase node — and the circulating 3-phase flow proposal
should cite the format registry (§2) as its versioning substrate.

## 2. The manifest convergence (RESOLUTION — adopt as a named workstream)

Independent reviews of nine different lanes each demanded the same
missing object. Codex asked for: a five-identity transitive manifest
(decoder/schema revision; producer/toolchain; public semantic
interface; implementation content; full action key); instance-
environment and dictionary-evidence digests in action keys (coherence);
codebook fingerprints in semantic identity (HuffmanBits); schedule
digests keying schedule-scoped facts (port properties); FFI transport
and ABI descriptors (DPI/VPI); binding + tier + trust + capability
profiles (BVI fallback); engine/fallback honesty manifests and
fail-closed strict modes (trs); X-policy vectors in artifacts and
certificates (ValidateBits); resolved source closures and final-name
maps (verilator check-only); versioned action-keyed reply envelopes
(LSP). These are one artifact family, not ten features.

RESOLUTION: the artifact-graph program gains an explicit first node —
the **format registry and transitive manifest** — and it is the DAG's
root (see 08). Concretely:

- One registry of format tags (.bo, .ba, BIR, snapshots, plans, AOT
  layouts, callback ABIs) with rules for compatible vs breaking
  changes; readers reject unknown semantic fields (never skip-and-run);
  every serializer bump goes through the registry. The PR-144/47
  no-bump findings and the AOT rev-26 callback-ABI reuse are the
  motivating defects (FACT).
- One manifest schema carrying the five identities, with field
  ownership; attached to every durable artifact and validated by every
  loader. Bindings (implementation selections, tiers, tool pins,
  transports, X-policy vectors, capability profiles) live here.
- Fail-closed doctrine: a strict mode (TRS_REQUIRE_AOT and kin) rejects
  every fallback path including in-process recompilation; unclassified
  = non-cacheable; unknown = refuse. "A launcher is not an immutable
  artifact" — artifact identity is verified by digest before execution.

## 3. Interning, serialization, and the session context

FACT: the interning line is proven — IType hash-consing with cached
metadata (WHNF-only rnf, ftv sets, ATF-free bit), IExpr fv caches +
content hashes + rank-first Ord (a real Ord-law fix), measured wins and
measured taxes, chicken flags throughout. The artifact-graph's
serialization strategy ("intern what you save, exempt what you unify";
serialize the reachable walk-ordered projection; derive the tree-shaped
residue; CType as a phase-indexed structure) builds on it.

RESOLUTION — the **session-context program**. Four independent reviews
converge on one structural demand: process-global state must move into
an action-scoped context. The instances: IType's three global intern
tables (unbounded, name-keyed, stale across package revisions); the
ATF reduction memo (keyed by intern unique but dependent on the
caller's rule universe); LLVM -time-passes globality; the LSP's
long-running worker; rung 4 of the parallelism ladder (in-process
node-level parallelism blocked on the reentrancy audit). Adopt Codex's
frame: one **CompilationSession/QueryContext** owns the interner arena,
the frozen rule/instance snapshot, and every unique-keyed memo, with
three declared lifetimes — (i) node-local structural metadata (valid
forever on immutable nodes), (ii) out-of-node structural acceleration
(valid per arena generation), (iii) environment-dependent results
(valid per semantic snapshot). No memo outlives its environment or its
interner generation; intern ids never enter durable identity (rename
IExpr's "content hash" to *comparison fingerprint* per the retired
objection). This program is a prerequisite for ladder rung 4, the LSP
worker, bluehs persistence, and constructor-time ATF folding — do it
once, not four times.

RESOLUTION — the phase-index (notes) refactor for IExpr is the by-type
successor of both chicken flags and should fold in type-level exclusion
of IRefT from the hashable phase; the ICDef/state-wire knots need the
exactly-once re-annotation argument; the eager-hash-at-unheap claim is
measured before relied on. (All accepted in-lane; recorded here because
the refactor is where the fv/hash taxes die.)

## 4. The definition cache and the eager layer

FACT: the pre-.bo eager layer (LiftDicts/fixupDefs/iSimpDicts/
iSimplify) breaks iface-keyed .bo identity today (an import's
dictionary inventory changes your bytes). The replacement — raw impl as
identity, per-definition simplified forms as a demand-populated durable
cache, dictionary dedup in the elaboration-time evidence cache — is the
ATF-cache pattern generalized ("three instances of one mechanism",
with CtxRed retirement P2).

RESOLUTION: keep the design; demote the "strict dominance" framing to
a hypothesis with the measurement plan attached (Codex's condition —
purity/compositionality of per-definition simp across SCCs is exactly
what the experiment must establish; the SCC semantics and the
two-stage/dynamic-dependency key shape are needed specification, not
disagreement). Warm-vs-lazy stays a policy spectrum ("eagerness returns
as cache-warming policy, not identity semantics").

## 5. Tests as graph nodes

The verdict-node discipline (artifact-graph §16 + testsuite-after-shake
v1.0) is settled in shape: cacheability classes earned by declaration
(hermetic / environment-scoped / non-cacheable; unclassified =
non-cacheable), asymmetric failure caching (deterministic failures
cache; infrastructure failures never), the gate ladder as graph
dependencies, periodic uncached audits, the never-link-the-bsc-under-
test rule, and the migration trigger "the engine landed" (upstream
premise; fork-only flips the verdict — do not migrate the corpus ahead
of upstream).

RESOLUTIONS folded from the reviews:

- **Capability visibility.** A capability profile (SystemC, simulators,
  root/non-root, licenses) is part of every verdict identity; an
  unavailable capability must read as *not covered*, never as a green
  skip. Historical seals that rationalized SystemC/root failures stop
  being acceptable; the repository gate for landing compiler changes is
  the clean non-root SystemC-enabled fullparallel run at zero
  unexpected failures (Codex's standing demand across five lanes;
  adopt it as the stated bar, with XFAIL for genuine expectations).
- **Register the orphan batteries.** Manual test scripts outside the
  authoritative suite (the trs BVI r2–r5 batteries are the concrete
  case) are silent-coverage debt: register them under the current
  fullparallel gate with stable check IDs before any orchestrator
  migration; dual-runs must prove the same *population*, not the same
  aggregate count.
- **Analysis observability.** Bounded analyses must export
  completeness (the pattern checker's fuel abandonment; provenStable/
  unknown in G0129) so cached verdicts and editor surfaces never read
  "no warning" as "proved".
- **Do now, orchestrator-neutral:** the S1 checker tools (timestamped-
  multiset comparator; Verilog alpha-equivalence; structured verdict
  emitter with stable check IDs), the cacheability census, and the
  stable check-ID scheme.

## 6. Build determinism and speed (FACTs with one open patch)

The GHC-side program: nondeterministic .o/.hi drift root-caused to
rule-selection order (findBest resolves specificity-incomparable
overlaps positionally; interface-load order is thread-scheduled); the
fix is a stable tie-break (GHC patch in validation; Codex asks for a
total key — add a structural fingerprint or reject duplicate keys).
Warmup + sane flags gives deterministic ~67s builds; GHCJOBS knee is
set by average module-graph width (~j12; ship `min(cores,16)` and
-A256m); one-shot builds are deterministic-by-construction but ~1.5×
slower. Profiling law: exempt leaf modules from -fprof-auto or the
profile fabricates cost. Methodology law (three strikes): every
load-bearing number needs a raw artifact behind it.

Under the artifact graph these become table stakes: deterministic keys
are hook #1 of the Bazel containment plan, and the bit-identical
double-compile is a CI invariant (July §4.5).

## 7. What lands where (pointers)

Mechanisms: RFC-bsc-artifact-graph.md §§3–6 (driver, ladder, nodes,
interning, CType index), §16 + testsuite-after-shake.md (tests),
§4 (Bazel). Reviews and adopted refinements: the KB lane "KB: bsc
artifact graph" carries every Codex block and its disposition. The
manifest workstream and session-context program of this document are
new names for demands spread across "KB: bsc typeclass coherence",
"KB: bsc ATF rewrite rules design", "KB: bsc IType interning perf
boundaries", "KB: bsc IExpr metadata and notes design", "KB: trs
full-AOT push", "KB: bsc semantic port properties", "KB: BVI-via-
Verilator design", "KB: bsc verilator integration", and "KB: Bluespec
LSP design".

## 8. NEEDS-RAVI (rolled up in 09)

- Ratify the manifest/format-registry workstream as the DAG root and
  the recertification set for the already-landed schema drift (PRs 47,
  66, 67, 87, 144, 151, 152 + AOT rev-26 callback ABI).
- Ratify the zero-unexpected non-root SystemC-enabled full-suite bar as
  the landing gate wording.
- Artifact-graph §14 sync to scheduling v0.4 (editorial; approve the
  supersession rewrite).
- Whether cabalization P1 (bsc-as-library) proceeds on the stdlib
  maintainer's line and when the rung-1 bsc-make sidecar gets built —
  noting the Cabal migration is now an upstream-prioritized decision
  and the Unison engagement plans a cabalize PR (10 §§1,3).
- Ratify the contract-files ↔ manifest unification (§1) so the 3-phase
  flow proposal and the artifact-graph RFC don't fork the format.
