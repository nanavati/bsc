# 06 — Developer Experience: bluehs, the LSP, and Typed Observability

The tooling program: the compiler as a library, the language server,
typed simulation control, and typed waves — and the one query surface
they converge on.

**Status:** v1.0 — 2026-08-24 (Claude, holistic review). Labels: FACT /
DECISION / PROPOSAL / RESOLUTION / NEEDS-RAVI.

## 1. bluehs

DECISIONS: bluehs proceeds (leadership-aligned, low-risk; tool delivery
independent of compiler releases); packaging is the fat `bsc-internals`
package exposing all ~226 modules, exact-commit, interfaces
deliberately undesigned until bluehs teaches us what it wants; the
freeze rule is *freeze only what bluehs cannot add later*. Provenance
(10 §§3,5): the May GHCi-integration proposal (load all compiler
modules into an interactive session for scripting and metadata
extraction) is the origin, and the posture is stated on the tour —
"who needs an API: access to all of BSC's libraries in Haskell, settle
to a sensible API once we understand what's useful"; the near-term
driver is lint-waiver emission scripting, and the release is promised
to outside collaborators for experimentation. bluehs is also the
stated replacement direction for the bluetcl/BDW lineage (BDW being
"a stress test for bluetcl").

RESOLUTIONS (adopting the review): the raw package is an exact-commit
exploratory API and never the blessed surface; the blessed surfaces are
small consumer-taught wrappers grown when consumers land. The eventual
component split (solver, Tcl, raw internals, simulation control as
separately-linked pieces — today every script inherits STP/Yices/Tcl
linkage) is that milestone's requirement, not v1's. Distribution
manifests carry source commit, schema, GHC ABI, platform, bk ABI, and
native pins (T2).

Scope facts from the meeting record (10 §§1,5; the freeze chats): SVA
cannot be delivered through bluehs — it involves processing different
source; the valuable adjacent items are next-design-scale. GHC 9.14's
GHCi change dramatically improves bluehs performance (01 §6), which
strengthens the 9.14-for-releases line.

**Simulation scripting** (PROPOSAL, evidence complete): a typed second
frontend over the same BluesimLoader/bk_* seam bluetcl uses — not a
Bluetcl replacement, not v1 scope, pulled in by a concrete consumer.
The bk_* ABI needs no additions for parity (it is strictly read-only;
bluetcl offers no write path either). NEW FACT bearing on the kernel
question: a **synchronous stepping API** (bk_sync_*) now exists on a
branch — inline single-stepping without the helper thread, ~340×
cheaper per step — built for model fuzzing (05 §5); it is read/step
control, not poke, but its author's fuzzing prototype will produce a
concrete hook-ask list, and the Bluesim-ABI freeze coordination item
(09 item 10) now has a named second stakeholder. Differentiators: typed state
decode through the recorded-types spine, property-based stimulus via
sidecar modules, invariant/coverage sidecars, and the same interface
driving trs artifacts unchanged (drop-in bk_* ABI). The natural first
consumer is the Bluesim-vs-trs lockstep differential driver — with the
review's condition adopted: in-process lockstep is not generally
independent (shared BDPI/stdin/files/RNG state); the first robust
consumer uses isolated workers or record/replay of external effects.
Interactive poke is the ONE candidate kernel extension and is weighed
separately (it costs freeze surface in both Bluesim and trs; the
sidecar-stimulus route covers most needs without it).

## 2. The LSP

Architecture (DECISION): two layers — an error-tolerant parser (bluehs
script code, differential-parse-tested against the identity-CI corpus,
promoted to normative only on receipts) plus bsc-as-library semantics
off last-good artifacts. Freeze rating B: tip-lane, freeze-indifferent.

The August joint scoping session (10 §3; full transcript now in the
lane draft) settled the operative design, refining this architecture:

- **Path-indexed ranges outside CSyntax**: ranges never go onto
  CSyntax (blast radius = the whole typechecker; and CSyntax is a
  *derived* artifact for the BSV front end, so any annotation scheme
  must live outside it regardless) — the parser produces the tree plus
  a path→range map; the typechecker stays essentially untouched and
  reports errors by path; comments become path-keyed annotations the
  same way. This is 04/01's carry-structure-forward thesis applied to
  diagnostics.
- **Parser modernization on Megaparsec** as the foundational first
  step (both parsers; source ranges; multi-error recovery; the
  implementing engineer took it as the codebase ramp) — answering the
  tour's parser complaints, with the recorded fact that a prior
  experiment bolting recovery onto the existing parsers made errors
  worse, not better.
- **Definition-level granularity; full incremental parsing REJECTED**
  (files are small, parsing is fast, LSP full-document sync suffices,
  no good Haskell incremental framework exists). Error recovery
  composes with partial compilation because mandatory top-level
  signatures let every definition typecheck independently —
  parse-error poison pills mirror the existing type-error mechanism.
- **A two-step proving ground**: parsers re-engineered, then
  range-based type diagnostics validated — each an independently
  useful compiler improvement that retires the core uncertainty before
  larger lifts.
- **BI interface files resurrected** as the persistent home for
  auxiliary metadata (ranges, docstrings) — converging with the
  independent check-only-mode motivation (01 §1: already
  reimplemented) rather than a parallel store.
- **Feature scope by consumer reality**: hover with type+docstring,
  go-to-definition, references, and type holes are the core; textual
  completions and renames are deprioritized *because LLM agents cover
  them* — agents are named a major LSP consumer class in their own
  right; waves-to-source navigation is judged adjacent UI space, not
  LSP proper (see §3). Multi-location diagnostics are verified
  possible in the protocol (the typeclass position-universe case);
  byte-based position encoding is negotiated explicitly.

The engagement's M1–M4 milestones track exactly these (parser →
BI files → range diagnostics → core editor capabilities); terms are
proposed, not agreed (07 §4.4). Touch-point tracing — named the single
most impactful feature in the May scoping — is a stated priority
WITHOUT a milestone; whether that is deliberate sequencing is an open
question (09). The rust-analyzer precedent governs parser status: a
non-official parser against the reference compiler is standard
sequencing, promotion is receipts-gated (with Codex's
incremental-edit-trace corpus as the proposed stronger gate).

One unreconciled alternative stands (10 §5): the lexer-modernization
arc judged a table-driven **LALR(1) port practical** (layout moves to
a lexer-side stack; error recovery nearly free), which sits beside the
Megaparsec decision as an open implementation question, not a second
decision. Shared step zero for docgen, hover docs, and any formatter:
**comments must survive lexing** (both current lexers discard them).
The measured Alex-lexer replacement (token-identical, byte-identical
rebuilds, up to ~6.3× on lexing-bound workloads, ~1.7× at large real
files) is the substrate either parser path builds on.
Feature priorities (DECISION, from the Unison scoping): the baseline
set (rename, references, hints); type-at-use-site (what compiler
integration buys over PR 891); **Verilog→source touch-point tracing**
(named most impactful); typed bit-vector unpack via the evaluator.
Build integration inverts: the LSP extracts the build graph and drives
itself from it — never generates build files. Portable baseline;
VS Code extras allowed.

RESOLUTIONS (adopting the review): semantic authority becomes a
versioned, action-keyed protocol — every reply binds workspace/config,
document version and buffer digest, snapshot and transitive action
identity, and classifies itself Exact / StaleLastGood / Pending /
Unavailable; stale semantics may display but never silently drive
refactors. The long-running worker cannot inherit process-global
compiler state — start with disposable workers keyed by action
generation; session reuse arrives with the session-context program
(01 §3). Source↔RTL provenance is a many-to-many DAG, not one selected
position (the multi-position open question is answered in that
direction). Typed decoding sandboxes with resource limits and a total
X/Z policy. Waveform correlation consumes final physical names — the
versioned AId-path→final-VId map (with aliases, inout rewires, scope,
width, role, decoder reference) feeds wiretypemap, BoundaryBinding, and
wave tooling alike; candidate-name heuristics are not the bridge.

Engagement (FACT): PR 891 is in daily use and stops where the compiler
starts; upstream wants an LSP and will review; the Unison DevEx program
is a severable staffing decision with funding pending (figures and
status in 07 §4.4, 09 A.3), with the proposal mechanics (rates, scope,
weekly status, shared channel) in motion per the August meeting; the
Bluespec, Inc. upstream-review program (same pending status) is the
governance counterweight. The longer-horizon
document independently rates the compiler-integrated LSP
contractor-friendly — well-specified, self-contained, no internal
context needed — which is the delivery-model argument for the
engagement (10 §4). The LSP acceptance bar placeholder ([RAVI: bar])
remains open in the memo.

## 3. Typed observability (the decoder witness)

One artifact serves every consumer (RESOLUTION, from 02 §3 + the
BVI/waves lanes): generated **decoding functions** (not static type
tables — Bits instances can be custom), total over 4-state input, X/Z
propagation defined per decoder kind (derived: per-field localization;
custom unpack: whole-value X), keyed by type + resolved Bits dictionary
+ codebook fingerprint + compiler schema, delivered in-artifact (trs
online decode) or as sidecars/viewer filters (the bluetcl-over-GTKWave
route, which also serves the Verilog flow's waves). Consumers: LSP
hovers and unpack, trs typed waves (arena slots carry BIR types →
Surfer translator + type sidecar, per-rule WILL_FIRE tracks — a
committed direction), VCD/FST tooling, BVI boundary ports (typed via
the contract even though the model is untyped), ValidateBits.

Dump policy (DECISION): the waveform signal set follows Bluesim for
now; Bluespec-typed dumping is the recorded aspiration; trs dump
throughput has a named eventual direction (write-time dirty sets, then
an AOT-emitted specialized dump walk) behind a benchmark tripwire.
The trs BVI observability tiers (boundary dump riding trs's
format-agnostic sink; link-time traced model variants as distinct cache
classes with per-instance side files) remain OPEN pending Ravi.

Meeting-record additions (10 §§5–6): a July decision restructured wave
generation to support **three dump formats selected by user
configuration** — the format-agnostic-sink posture above, arriving in
bsc itself; the waveform→source mapping ambition is stated on the tour
as a Verdi-class feature targeted at **Surfer** (chosen because it
decomposes structs and tagged unions properly), confirming the Surfer
translator direction; and the ramp menu carries the small complementary
item of emitting **Bluespec-type comments on generated ports,
registers, and wires** (comment syntax following the source language) —
the human-readable shadow of the decoder witness, worth keeping
consistent with it rather than independent.

The credentialed crawls (10 §§4–5) then filled in the working plan:

- **Wave-to-source is feasible today without forking Surfer**: Surfer
  speaks WCP and implements a goto_declaration event carrying the
  signal's full hierarchical path; the tool-side work is a WCP client
  plus a path→Bluespec-source map from bsc position info. The elegant
  endgame is one editor-side WCP client serving Surfer *and* Verdi (a
  Verdi-side Tcl script speaking the same JSON protocol — hooks
  unverified until the local manuals are read). The bsc-side piece is
  shared across all routes.
- **The type-sidecar plan** (the surfer-integration working doc): bsc
  emits a companion file mapping dumped signals to source types; a
  Bluespec translator for Surfer consumes it, making the wave format
  irrelevant to decoding. Container ruling: **FST over VCD** — FST
  scope records carry a slot for the module type, which VCD simply
  lacks (the VCD-comment convention was dropped as a hack around a
  format gap); Bluesim has FST support now; the FSDB path goes through
  fst conversion until direct-read licensing is worth raising. A
  March-era decoder-plugin proof of concept exists with a recorded
  shortcut list; adoption is honestly zero until the decoding ships
  ("never delivered the decoding that would make it better than
  Verdi").
- **The position-tracking doctrine** (Ravi, 2026-08-24): coverage and
  wave-to-source both benefit from better position tracking through
  the evaluator; state-element positions are already good, and both
  consumers may care about *intermediate* signals — one evaluator
  position-propagation investment, two named consumers (05 §6's
  workstream B display upgrade, and wave-to-source on non-state
  signals).
- **The agent-consumer reframing** (the portfolio transcript): a
  quality capture of state and events plus a command-line probe tool
  lets an agent hunt bugs at far lower cost than a human viewer — and
  the signals worth capturing typed are exactly the state elements and
  ports (everything else is a function of state; record state +
  CAN_FIRE/WILL_FIRE events, not full evaluation). This reframes the
  decoder witness's first consumer as possibly a probe tool rather
  than a viewer, without changing the artifact.

## 4. One query surface (the convergence)

From artifact-graph ladder rung 2 onward, the engine lives in the
library: bluetcl, bluehs, the LSP, and the test orchestrator consume
the same memoized, snapshot-keyed query surface over artifact nodes
(a stable worker/query protocol is the DAG's terminal node — 08). The
session-context program (01 §3) is its precondition. Bluetcl neither
grows nor deprecates: one implementation, two frontends; bluetcl keeps
the interactive-shell half and the EDA-familiar surface; the testsuite
keeps its 23 interactive .cmd tests as the parity anchor.

## 5. Lane pointers

"KB: bluehs simulation scripting design"; "KB: Bluespec LSP design";
"KB: bsc toolchain" HEAD (bluehs section; wiretypemap/porttypes
scaling); "KB: BVI-via-Verilator design" §9 (observability, decoders);
"KB: bsc verilator integration" (final-name map objection); "KB: trs
full-AOT push" (typed waves, Surfer); "KB: HuffmanBits" (codebook
witness); bsc PR 891; upstream #503, #1002.

## 6. NEEDS-RAVI (rolled up in 09)

- The Unison engagement decision (with the staffing memo) and the LSP
  acceptance bar; whether touch-point tracing's absence from M1–M4 is
  deliberate sequencing.
- The Megaparsec-vs-LALR(1) parser-implementation question (§2) — an
  open implementation choice under the settled modernization decision.
- bluehs sim-scripting: ratify the PROPOSAL's v1 bar (parity without
  poke) and the first-consumer choice; the poke/deposit kernel
  extension question — now coupled to the bk_sync/fuzzing hook-ask
  coordination (05 §5).
- trs observability tier 2 and the dump-default flip after the traced-
  run benchmark.
