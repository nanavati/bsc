# The Bluespec/trs Design Book

Where bsc and trs are going, and why.

**Status:** v2.0 — 2026-08-24. Synthesized by Claude at Ravi Nanavati's
direction from the complete cross-agent knowledge base, the canonical
RFCs, the per-lane design records, the review corpus, and the meeting/
document record. **This book is design, not plan**: documents 00–07
describe the destination architecture and its rationale, and 08
collects the open design questions — the destination choices still
needing Ravi's ruling. How we get there — landing order, migration
steps, gates, status, provenance — is entirely separate, lives in the
KB lanes (the per-lane drafts and the meeting-notes digest) and the
RFCs' own migration sections, and is deliberately not planned further
until the destination is agreed. MatX-specific considerations enter
the design documents only as **use-model requirements** (static
hermetic builds and caching, byte-stable artifacts, VCS and encrypted
IP, generated-type scale, agent-driven development — collected in 07);
MatX deployment history, schedules, and organization never do.

Where a statement here disagrees with a cited RFC's current revision,
the RFC governs on mechanism and this book governs on cross-lane
resolution until the RFC is updated. Labels: FACT (established, with
evidence), DECISION (ratified by Ravi), PROPOSAL, RESOLUTION (this
review's cross-lane call, adopted unless Ravi objects), OPEN (a design
question). Process/status labels do not appear in 00–07.

---

## 1. The map

- **00 (this document)** — the unifying theses and the vision.
- **01 — Identity, artifacts, and the build.** The compiler as a graph
  of typed durable artifacts; identity as content plus declared
  schema; the manifest layer; the session architecture; tests as
  graph nodes; determinism as a designed property.
- **02 — Boundaries and contracts.** The semantic/physical split;
  contracts as values; one owner for the port ABI; encodings as ABI;
  import "BVI" unified; foreign functions; instance-specific
  synthesis; the dissolution of genC/genVerilog; the SystemVerilog
  interop ABI.
- **03 — Scheduling.** One order; positions as the names of
  scheduling; schedules as values and contracts; footprints; dynamic
  schedules; the observable-event contract.
- **04 — The front end.** Coherence and closure; orphan enforcement;
  ATF evaluation; identity-not-cache for solved facts; the numeric
  engine; the metadata substrates; pattern checking.
- **05 — Simulation and verification.** The trs architecture; the X
  program; the reset and finish contracts; the oracle discipline; the
  coverage program; Bluesim's designed role.
- **06 — Developer experience.** The LSP; bluehs; typed observability;
  the one query surface; the parser/lexer modernization.
- **07 — Use models.** The two use models this design serves, stated
  as requirements; where their requirements genuinely conflict, and
  the design postures that resolve or contain each conflict.
- **08 — Open design questions.** The destination choices that need
  Ravi's ruling for this design to be agreed.

The normative artifacts this book organizes (not replaces):
RFC-bsc-artifact-graph.md, RFC-polymorphic-scheduling.md,
testsuite-after-shake.md, RFC-simulation-reset-sequence.md, the
post-genwrap design, CTXRED-RETIREMENT-PLAN.md, the trs design
documents, the SV-interop ABI doctrine note, the coverage proposal,
and the per-lane KB design records. Homes, versions, and provenance are
indexed in the KB (the bootstrap index and the meeting-notes digest).

## 2. The unifying theses

Nine theses recur across every lane. They are the design's identity;
each design document is one or two of them worked out.

**T1 — Everything the compiler knows becomes a value with provenance.**
Contracts, schedules, clocks, resets, X policy, encodings (codebooks),
bindings, obligations, diagnostics, test verdicts: each is reified as a
typed value carrying its position on the provenance lattice
(derived / asserted / validated). A fact the compiler
recomputes-and-discards at a boundary is a contract field waiting to
be named. The one-sentence form: *compiler contracts move from
inferred-and-implicit to declared-certified-pinned — layouts,
schedules, X.*

**T2 — Identity is content plus declared schema.** Cache keying, API
versioning, and format tagging are one mechanism: every durable node
carries a schema/pass version; a representation change bumps the tag;
the bump invalidates exactly the affected cache entries and is
simultaneously the version signal a consumer reads. Corollaries: the
canonical serialization of a contract value is the cache key of the
specialization providing it; instance/dictionary evidence and codebook
fingerprints are ABI identity, not implementation detail; intern ids
and heap identities never leak into durable identity.

**T3 — Facts flow up; models flow down; nothing is ambient.** Partial
orders, contracts, and landmarks flow up into signatures and
lockfiles. Solver models, linearizations, chosen realizations, and
simplifier outputs flow down as pinned artifacts recorded with what
they produced. Re-deriving a model ambient at consumption time is the
bug class this rule deletes.

**T4 — Judgment is the typechecker's monopoly; everything else
evaluates.** Open-world reasoning — instance selection under
refinement, improvement, deferral — happens exactly once, in the
typechecker, and its results are consumed into signatures. Every
persisting phase downstream evaluates over sealed, closed, coherent
fact sets. The licensing theorem, once: *early commitment is
meaning-preserving exactly when the match is coherent AND closed*
(type-closed and world-closed). Sealed ATF families, the orphan ban,
and ordered-clause commitment are its enforcement at three levels.

**T5 — One structure, many realizations.** The semantic contract /
physical realization split (IfcContract vs BoundaryBinding) is the
master instance; structural-vs-macro realization, engine-agnostic
module boundaries, per-instance realization selection at link time,
and the dissolution of genC/genVerilog into per-instance capability
requests are the same cut applied again. Design for type and
schedule/clocking compatibility, never wire compatibility — port names
stop being API.

**T6 — The scheduler stops being an optimizer and becomes a checker.**
One order (DECISION). Positions are the missing names of scheduling;
footprints are the contract representation; pairwise matrices are
derived views; maximize-firing gives way to stated intent;
over-constrained is an error, never a search. The EHR dissolves into a
register observed at many points; the FIFO zoo dissolves into one
polymorphic text.

**T7 — Verification is by witness, and replacement requires proof.**
Byte-exact differential oracles with succession plans; dual-flavor
seals; sealed corpora; X-freedom certificates. The governing sentence
(Ravi): trs replacing Bluesim requires *proving we don't need X, not
asserting it*. Correctness is never established by review or by the
absence of warnings — and because oracles are blind to provenance,
every claim also carries fail-closed telemetry.

**T8 — Carry structure forward; never discard-then-reconstruct.**
Path conditions, schedule footprints, branch structure, boundary
facts, source positions: discarding structured intent early and
paying a quadratic, solver-assisted price to approximate it back is
the compiler's historical failure shape. The cure has one form — keep
the structure; run expensive machinery only on the residue; persist
generators, never materialized views.

**T9 — Two use models, one architecture.** A fork, a pin, or a mode is
a *binding choice recorded in a manifest*, never an unrecorded
divergence. Requirements from either use model (07) enter the design
as declared, versioned inputs — not as environmental assumptions.

Named corollary principles:

- **Single source of truth.** Any fact with two consumers is computed
  once in one owned place; every other copy is a generated, checkable
  projection. Independent re-derivation is where silent divergence is
  born.
- **Fail closed; name every residual.** When a property cannot be
  established, the system stops with a named, ledgered reason. Silent
  fallback, silent coverage loss, and zero-fill are one bug class; the
  ledger of loud refusals *is* the roadmap.
- **The hardware-model line** (DECISION, Ravi). Primitives model real
  hardware; simulation-only behavior never enters their synthesizable
  semantics. Simulator-emulation gaps are closed by per-test simulator
  configuration or honest expected-failure markers — never by teaching
  library primitives extra initialization semantics.
- **Modal vs committed judgment.** Anywhere the toolchain commits
  early, viability checks run unguarded: a guarded modal check turns
  "not yet" into "never", and in a commitment regime "never" is what
  licenses a commit.

## 3. The vision

**The compiler becomes a graph of typed, durable artifacts.** The
driver is a build engine over a node vocabulary that is itself the
public API; bluetcl, bluehs, the LSP, and the test orchestrator
consume one memoized, snapshot-keyed query surface; the testsuite is
the graph's largest consumer, its verdicts first-class cached nodes.
The same graph is containable by an outer static, hermetic build
system — a use-model requirement (07) designed in from the start via
frozen specialization manifests, not retrofitted. The compile pipeline
itself decomposes into phase executables whose inter-phase artifacts
are contract-carrying, cacheable values — the smaller-tools direction
and the artifact graph are one design seen from two sides: a phase
boundary deserves a process seam exactly where its artifact earns
caching, parallelism, or a second consumer.

**Boundaries become contracts; implementations become bindings.**
Every synthesized boundary factors into a semantic contract and a
physical realization, joined by a witness; backends gain symmetric
segment/link seams so any conforming realization substitutes at link
without re-elaboration — "elaborate once, simulate many ways."
import "BVI" decomposes into an asserted contract plus a foreign
realization; fallback and soft-IP become structural, taint-free
bindings; instance-specific synthesis serves polymorphic imports; and
genC/genVerilog dissolve into per-instance realization capabilities.
An undischarged obligation is an error — IP integration stops being a
silent-unsoundness channel. The rendering of Bluespec types into
SystemVerilog and Rust is governed as one ABI, emitted from one
type-to-rendering library.

**Scheduling becomes a typed dimension of the language.** Positions as
a kind; schedules as values (bindings of position variables);
footprints as boundary contracts; the compiler checks stated
schedules rather than inferring and imposing them; the schedule
lockfile joins the build; a totally-specified (Kôika-style) mode is
the endpoint of the fill dial. Interface arguments — dropped
historically because the compiler couldn't capture their scheduling —
return as a natural beneficiary once footprints ride interfaces.

**The front end becomes coherent, closed, and raw-identity.**
Instance resolution commits only under the closure theorem, and its
evidence is carried, digested, and ABI-bearing; orphan instances of
representation-owning classes are use-site errors; ATF families are
sealed and reduce by pure ground evaluation everywhere outside the
typechecker; the written form is identity and solved facts are a
cache — which is what unblocks visible type application and
born-reduced deriving; numeric solving grows along three named axes
under the ceiling "complete where decidable, axiomatic where not —
no uncheckable or non-monotone acceptance." Beyond that lie
implication constraints, higher-rank types, and GADT-style reasoning.

**trs becomes the reference simulation platform; Bluesim becomes the
designated-world evaluator.** trs is hierarchical, flavor-transparent,
and staged into small tools over durable artifact boundaries;
per-module fragments carry interface/body hashes so separate
compilation just works; module boundaries are engine-agnostic with
fusion regions, so compiled, interpreted, and verilated-leaf
implementations interchange per instance; the shell speaks the
established generated-Verilog port protocol so trs drops into
existing flows. The X program makes 3-state trs the reference
semantics with a 2-state benchmarking mode, and aims to *prove* X
unnecessary per design, with certificates; Bluesim remains the
byte-parity oracle and world-sampler. Replacement is earned by proof
and identity discipline, not declared.

**Observability and coverage become typed and structural.** One
fingerprinted decoder/validator witness per encoding-owning instance
serves waveform decoding, state inspection, validity checking, and
editor hovers; wave-to-source navigation rides a small protocol
client plus a compiler-emitted type sidecar; coverage is emitted by
the compiler — the last tool that still sees design meaning — as
rule/conflict/mux-arm/select-point instruments and type-driven
covergroups with structural point identity, so accumulated coverage
survives position-fidelity improvements. One evaluator
position-propagation investment serves both consumers. Agents are a
first-class consumer: quality state-and-event capture plus a probe
tool can matter more than human viewers.

**The ecosystem grows without capture.** Compatibility breaks are
measured, named, and versioned; upstream-facing changes ship with
their censuses; fork-only capabilities stay fork-scoped with explicit
upstreaming decisions; stewardship is designed so no
single contributor becomes a de facto owner. The design is
upstream-shaped by default; the use-model requirements of 07 are
declared inputs, not forks of the truth.

## 4. How to read this set

Read 00 → the area documents you own → 07 for the use-model
requirements → 08 for what still needs deciding. Every design document
ends with its RESOLUTIONS and its OPEN questions; 08 collects
everything needing Ravi.

**Editorial law.** A sentence belongs in this set iff it would still
be true and useful after every currently-open PR lands or dies. These
documents carry no PR numbers, no branch names, no landed/pending
status, and no dates-as-status; measured evidence appears only as the
rationale for a design choice, stated as a finding. Status ledgers and
sequencing live in the KB lanes and the RFCs' migration sections;
provenance lives in the KB meeting-notes digest. Planning how to get
there is deliberately deferred until this destination is agreed. The
KB remains the review surface: responses belong in the KB lane
drafts, per the cross-agent protocol.
