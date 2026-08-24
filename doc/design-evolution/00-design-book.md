# The Bluespec/trs Design Book

A canonical map of the design evolution of bsc and trs — the theses, the
documents, the resolutions, and the long-term vision.

**Status:** v1.1 — 2026-08-24. Synthesized by Claude at Ravi Nanavati's
direction from a holistic review of the complete cross-agent knowledge
base (30 KB drafts, snapshot 2026-08-23/24), the two canonical RFCs, the
per-lane design records, Codex's review corpus, and (v1.1) the meeting-
notes crawl — Gemini summaries for every Bluespec meeting and
compiler-team 1:1 March–August 2026, the compiler-tour transcript, and
the Bluespec Drive folder. This document set organizes and resolves; it
does not replace the RFCs it cites. Where a statement here disagrees
with a cited RFC's current revision, the RFC governs on mechanism and
this book governs on cross-lane resolution until the RFC is updated.
Labels follow the KB convention: FACT, DECISION (ratified by Ravi),
PROPOSAL, RESOLUTION (this review's cross-lane call, adopted unless
Ravi objects), NEEDS-RAVI. Organizing rule: **MatX-specific facts
(deployment, corpus, schedule, organization) live only in 07**; every
other document is written to be readable as Bluespec/trs design record
and cites 07 where a deployment fact grounds a claim.

---

## 1. What this is

Through 2026, the Bluespec compiler (bsc) and the trs simulator
accumulated a large body of design work spread across many lanes:
two RFCs, a dozen design records, several implemented-but-unlanded
substrates, a trs rung ledger, and hundreds of review findings. Each
lane is locally coherent; what was missing was the whole. This book and
its companion documents are that whole:

- **00 (this document)** — the unifying theses, the vision, and the map.
- **01 — Identity, artifacts, and the build.** The artifact-graph
  program and everything that keys off it: nodes, interning, schema
  tags, manifests, Shake, Bazel containment, the testsuite migration,
  build determinism.
- **02 — Boundaries and contracts.** The semantic/physical split,
  contracts as values, BVI in all its forms, the port ABI and its
  witnesses, instance-specific synthesis, the retirement of
  genC/genVerilog.
- **03 — Scheduling.** The one-order model, positions, footprints, the
  migration, and the reconciliation with engine phase machinery.
- **04 — The front end.** Coherence, closure, CtxRed retirement,
  visible type application, ATF evaluation, deriving, the numeric
  engine, pattern checking, and the metadata substrates.
- **05 — Simulation and verification.** trs architecture doctrine, the
  full-AOT campaign, BVI-via-Verilator, the X program, oracles and
  seals, Bluesim's role, and the Verilog-harness contract.
- **06 — Developer experience.** bluehs, the LSP, typed simulation
  control, typed waves, and the query surface they share.
- **07 — Two worlds.** Where upstream Bluespec and MatX pull in
  different directions, and the posture per lane.
- **08 — Landing order.** The cross-lane dependency DAG, per-node
  status, and the gates.
- **09 — Open questions.** Everything that needs Ravi, consolidated
  and prioritized.
- **10 — The meeting record.** The Bluespec decision timeline outside
  the KB: the open-source syncs (including the smaller-tools decision),
  the upstream engagement program, the LSP/Unison arc, the
  longer-horizon project set, and compiler-internals facts first
  recorded in meetings.

The already-canonical design documents this set organizes (not
replaces):

| Document | Home | Status |
|---|---|---|
| RFC-bsc-artifact-graph.md v0.21 | nanavati claude/bsc-testsuite-cabal-dejagnu-cscgl9 | Draft; mirrored in KB |
| RFC-polymorphic-scheduling.md v0.4 | same branch | Draft; mirrored in KB |
| testsuite-after-shake.md v1.0 | same branch | Analysis; mirrored in KB |
| post-genwrap-compiler.md (July 2026) | nanavati claude/model-rqj7c1 | Ancestor of the contract program |
| CTXRED-RETIREMENT-PLAN.md (+ BA-contracts review) | nanavati claude/proposal-adversarial-review-ccew7z | Plan v0.1 + in-KB extensions |
| doc/RFC-simulation-reset-sequence.md | nanavati claude/reset-sequence | Implemented + validated |
| typechecker-coherent-instance-commitment (dev note) | nanavati claude/typechecker-coherent-instances-dkmn8w | Pre-carve; digest in KB governs on vocabulary |
| trs design docs (DESIGN.md, BIR.md, BOUNDARY-CONTRACT.md, v5 BVI doc) | MatX-inc/bsc trs stack + KB | As-built + doctrine |
| Per-lane KB design records (ValidateBits, SplitPorts, IExpr, IType, ATF, port properties, HuffmanBits, BVI fallback, solver strategy, LSP, bluehs, toplift, open-packed DPI, pattern-match) | Gmail KB drafts | Review surfaces |

## 2. The unifying theses

Nine theses recur across every lane. They are the design's identity;
each companion document is one or two of them worked out.

**T1 — Everything the compiler knows becomes a value with provenance.**
Contracts, schedules, clocks, resets, X policy, encodings (codebooks),
bindings, obligations, diagnostics, test verdicts: each is reified as a
typed value carrying its position on the provenance lattice
(derived / asserted / validated). The pattern was set by the July 2026
post-GenWrap design (IfcContract, licenses) and generalizes without
exception. A fact the compiler recomputes-and-discards at a boundary is
a contract field waiting to be named (the enumeration principle).

**T2 — Identity is content plus declared schema.** Cache keying, API
versioning, and format tagging are one mechanism: every durable node
carries a schema/pass version; a representation change bumps the tag;
the bump invalidates exactly the affected cache entries and is
simultaneously the version signal a consumer reads. Corollaries: the
canonical serialization of a contract value is the cache key of the
specialization providing it; instance/dictionary evidence and Huffman
codebook fingerprints are ABI identity, not implementation detail;
intern ids and heap identities never leak into durable identity.

**T3 — Facts flow up; models flow down; nothing is ambient.** Partial
orders, contracts, and landmarks flow up into signatures and lockfiles.
Solver models, linearizations, chosen realizations, and simplifier
outputs flow down as pinned artifacts recorded with what they produced.
Re-deriving a model ambient at consumption time is the bug class this
rule deletes (asch_rev_exec_order is the in-tree precedent; the
scheduling RFC's pinned-model rule and the port-properties one-plan
demand are the same law).

**T4 — Judgment is the typechecker's monopoly; everything else
evaluates.** Open-world reasoning — instance selection under
refinement, improvement, deferral — happens exactly once, in the
typechecker, and its results are consumed into signatures. Every
persisting phase downstream evaluates over sealed, closed, coherent
fact sets: ATF ground evaluation, elaboration's ground solves, the
definition cache. The licensing theorem appears three times in the
corpus and is one theorem: *early commitment is meaning-preserving
exactly when the match is coherent AND closed* (type-closed and
world-closed). Sealed ATF families, the orphan ban, and ordered-clause
commitment are its enforcement at three levels.

**T5 — One structure, many realizations.** The semantic contract /
physical realization split (IfcContract vs BoundaryBinding) is the
master instance; structural-vs-macro realization, engine-agnostic
module boundaries (trs fusion regions), per-instance realization
selection at link time, and the dissolution of genC/genVerilog into
per-instance capability requests are the same cut applied again.
A20 governs: design for type and schedule/clocking compatibility,
never wire compatibility — port names stop being API.

**T6 — The scheduler stops being an optimizer and becomes a checker.**
One order (DECISION, Ravi 2026-08-23). Positions are the missing names
of scheduling; footprints are the contract representation; pairwise
matrices are derived views; maximize-firing gives way to stated intent;
over-constrained is an error, never a search. The EHR dissolves into a
register observed at many points; the FIFO zoo dissolves into one
polymorphic text.

**T7 — Verification is by witness, and replacement requires proof.**
Byte-exact differential oracles with succession plans; dual-flavor
seals; prediction ledgers scored HIT/MISS; sealed corpora; X-freedom
certificates. The governing sentence (Ravi): trs replacing Bluesim
requires *proving we don't need X, not asserting it*. The bar of record
on any design is the fastest opponent's wall.

**T8 — Carry structure forward; never discard-then-reconstruct.**
Path conditions, SchedInfo footprints, branch structure, boundary
facts: the compiler historically threw away structured intent early and
paid a quadratic, solver-assisted price to approximate it back. The
cure has one shape — keep the structure; run expensive machinery only
on the residue. (The scheduler transpose, the -sched-conditions
analysis, footprints-not-matrices, and generators-not-tables are all
this thesis.)

**T9 — Two products, one architecture.** Upstream bsc evolves by RFC,
staged migration, and compatibility censuses; MatX rides pinned tools,
side-trees, and manifest-keyed caches. The same identity discipline
serves both: a fork, a pin, or a mode is a *binding choice recorded in
a manifest*, never an unrecorded divergence.

Two corollaries the cross-cut theme analysis states crisply enough to
adopt as named principles (they refine T3/T5/T7 rather than adding
theses): **single source of truth** — any fact with two consumers is
computed once in one owned place, and every other copy is a generated,
checkable projection, because independent re-derivation is where silent
divergence is born; and **fail closed, name every residual** — when a
property cannot be established the system stops with a named, ledgered
reason, and the ledger of loud refusals *is* the roadmap. The
cross-cut's fuller twelve-theme decomposition maps onto T1–T9 and is
preserved in the review's working notes.

## 3. The vision, as a narrative

Where this all converges if pushed to completion — distinguishing what
the lanes already claim (cited) from extrapolation (marked).

**The compiler becomes a graph of typed, durable artifacts.** bsc -u is
the Shake engine (artifact-graph §3); the node vocabulary is the public
API (§6); bluetcl, bluehs, and the LSP consume one memoized query
surface; the testsuite is the graph's largest consumer (~48k verdict
nodes, §16); an outer static build system contains the same graph
through tree artifacts, workers, a remote-execution share, and frozen
manifests (§4; the deployed instance in 07). Upstream's own
smaller-tools decision — the 3-phase compile split with contract files
(10 §1) — is this program arriving from the build-integration side.
Extrapolation: the same verdict/manifest discipline eventually carries
a customer's full RTL CI — a compiler change re-runs compiles plus only
the genuinely affected legs, fleet-wide, with cached PASS a soundness
claim rather than an optimization.

**Boundaries become contracts; implementations become bindings.**
VModInfo splits into IfcContract × BoundaryBinding with the .ba as the
witness that connects them; Verilog gains vseg/vlink and completes the
backend symmetry with Bluesim and trs; import "BVI" decomposes into an
asserted contract plus a foreign realization; the BVI-fallback clause
makes real-IP-vs-model a structural, taint-free binding; instance-
specific synthesis serves polymorphic imports; and genC/genVerilog
retire into per-instance realization capabilities, splitting the
expensive backend-neutral prefix (parse, typecheck, elaborate,
schedule, contracts, symbolic segments) from small binding-keyed
codegen leaves. Constraint obligations ride bindings and an
undischarged obligation is an error — IP integration stops being a
silent-unsoundness channel.

**Scheduling becomes a typed dimension of the language.** Positions as
a kind; schedules as values (bindings of position variables);
footprints as boundary contracts; the schedule lockfile; Kôika mode as
the endpoint of the fill dial. The migration's first three steps
(footprint artifact, schedule value type + one-order census, verify
mode) are independently shippable and useful.

**The front end becomes coherent, closed, and raw-identity.** The
coherence stack (#1032–#1038) lands upstream; orphan instances of
representation-owning classes become use-site errors; ATF families are
sealed-or-nonoverlapping and reduce by pure ground evaluation
everywhere outside the typechecker; CtxRed retires with written
telescopes as identity and solved facts as caches — which is what
unblocks visible type application; deriving becomes born-reduced;
numeric solving grows along three named axes under the policy ceiling
"complete where decidable, axiomatic where not, heuristic never"
(NEEDS-RAVI to ratify). Extrapolation: with implication constraints and
the inert-set store, numeric-refinement case statements, higher-rank
types, and GADT-like reasoning become reachable — the front end's
2027+ growth direction.

**trs becomes the reference simulation platform; Bluesim becomes the
designated-world evaluator.** The doctrine of record (Ravi, 2026-08-22/23):
frozen-bsc side-tree; flavor-transparent BIR with the dual-flavor seal;
the trs porcelain (trs-bir / plan / emit / ld / run / shell) with
durable artifact boundaries; per-module fragments with interface/body
hashes; engine-agnostic module boundaries with fusion regions
("the interpreter boils away only under the full compile"); -O re-fuse;
trs shell speaking the 26-year generated-Verilog port protocol over
DPI. The performance campaign's endpoint is "nothing walked per cycle";
Toooba is at Verilator parity and wire-heavy internal shapes are well
ahead of Bluesim already (FACT, corpus-conditional; numbers in 07). The
X program
makes trs 3-state the reference semantics, keeps a 2-state benchmarking
mode, and aims to *prove X unnecessary* per design, with certificates.
Bluesim remains production until that proof program and the manifest/
fail-closed identity rungs land — replacement is earned, not declared.

**Observability becomes typed.** Bluespec-typed waveform decoding via
generated decoding functions (total over 4-state, X/Z policy per
decoder kind), delivered in-artifact or as sidecars serving the Verilog
flow's waves too; arena slots carrying BIR types feeding a Surfer
translator; Verilog→source touch-point tracing as the LSP's headline
feature; bluehs typed simulation control over the same bk_* seam trs
already implements. Extrapolation: the "one dictionary-keyed decoder
and validator artifact" (Codex) becomes the single witness consumed by
LSP hovers, wave viewers, trs state inspection, and ValidateBits — one
codebook, everywhere, fingerprinted into identity.

**The ecosystem grows without capture.** Upstream persuasion is staged
(S0–S4 staircases, censuses before proposals); compatibility breaks are
measured, named rungs; the Unison LSP engagement and the Bluespec, Inc.
upstream-review program balance investment against de facto takeover;
fork-only capabilities (open-packed DPI, the pinned Verilator) stay
fork-scoped with explicit upstreaming decisions. The reset-sequence
RFC and the $random unification are the ecosystem-facing proposals in
waiting, and the longer-horizon set (compiler-integrated LSP, full SV
output mode, user-specified schedules, the import rethink; 10 §4) is
the stated destination beyond every current roadmap.

## 4. The state of the union (FACTs, 2026-08-24)

- **Landed/measured:** scheduler transpose (PR 47; 25× at 16k rules);
  trs rungs 1–40 (PRs #108–#158; all-AOT invariant; Toooba at Verilator
  parity; internal corpus byte-exact, zero known parity divergences —
  07); BVI-via-Verilator v5 as-built; reset-sequence + two-state-z +
  verilator timing arcs (iverilog fully green; every verilator failure
  named); ATF rules evaluator (fork PR 68/93 lineage); IType/IExpr
  substrates
  (measured, landing pending CI); semantic port properties (PRs
  #1059/#1060); pattern-match checker stack; prim-fixes + codegen
  stack-overflow fixes; wiretypemap/porttypes scaling; build
  determinism (GHC findBest patch in validation; Warmup).
- **Designed, awaiting decisions or prerequisites:** VTA (blocked on
  CtxRed P1); CtxRed retirement plan; BVI fallback/soft-IP; SplitPorts
  restructure (never compiled — gate on compile + bytes + capability
  matrix); ValidateBits (v3, mostly ratified); HuffmanBits generic
  deriving (gate (a)/(b) NEEDS-RAVI); solver strategy (policy ceiling
  NEEDS-RAVI); notes/phase-index refactor; bluehs sim scripting; LSP
  architecture.
- **The two RFCs** carry the structural program; their §12/§15 open
  questions plus Codex's unadopted objections are tracked in 08/09.
- **Known process debt:** the toolchain continuation draft is to be
  frozen; several Codex objections stand unanswered (PR #158 set,
  BIR fragment addressability, format-registry demands). The
  "bsc as smaller tools" gap is CLOSED: the sync record is recovered
  and indexed (10 §1); the remaining meeting-record gaps are the
  coverage proposal and two un-noted meetings (10 §7).

## 5. How to read this set

Read 00 → 08 → the area documents you own. Every area document ends
with its RESOLUTIONS and its NEEDS-RAVI items; 09 collects the latter.
The KB remains the review surface: responses to any of this belong in
the KB lane drafts, per the cross-agent protocol.
