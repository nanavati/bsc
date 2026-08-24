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

**Simulation scripting** (PROPOSAL, evidence complete): a typed second
frontend over the same BluesimLoader/bk_* seam bluetcl uses — not a
Bluetcl replacement, not v1 scope, pulled in by a concrete consumer.
The bk_* ABI needs no additions for parity (it is strictly read-only;
bluetcl offers no write path either). Differentiators: typed state
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

The August LSP meeting (10 §3) settled four working decisions that
refine this architecture: **path-based range indexing** decoupled from
the primary syntax tree (range data does not force syntax-type
modifications); parser modernization on **Megaparsec with error
recovery and multi-error reporting** — which simultaneously answers the
tour's parser complaints (multiple errors, better messages,
highlighting; neither existing parser library is worth reusing);
essential-features-first scope (stable navigation and type checking
before breadth); and **resurrecting interface files as the persistent
home for auxiliary metadata** (doc strings and kin) — which for this
document means the last-good-artifact layer reads an *enriched* .bo
lineage rather than a parallel store, consistent with the tour's
finding that .bo already carries I-syntax with positions and per-package
signatures but not source text. LSP position-encoding (byte-based
offsets) is handled explicitly at the protocol boundary.
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
(~$300K NTE) is a severable staffing-memo decision, with the proposal
mechanics (rates, scope, weekly status, shared channel) in motion per
the August meeting; the Bluespec, Inc. upstream-review program
(~$225K NTE) is the governance counterweight. The longer-horizon
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

Meeting-record additions (10 §5): a July decision restructured wave
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
  acceptance bar.
- bluehs sim-scripting: ratify the PROPOSAL's v1 bar (parity without
  poke) and the first-consumer choice; the poke/deposit kernel
  extension question.
- trs observability tier 2 and the dump-default flip after the traced-
  run benchmark.
