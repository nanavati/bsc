# 06 — Developer Experience: the LSP, bluehs, and Typed Observability

The tooling destination: the compiler as a library, the language
server, typed simulation control, typed waves and coverage display,
the parser/lexer modernization, and the one query surface they
converge on.

**Status:** v2.0 — 2026-08-24 (Claude). Design only; engagement terms,
staffing, and status live in the KB lanes, outside this set.

## 1. bluehs: the compiler as a library

The design: expose all of bsc's libraries in one exact-commit package
first, and let consumers teach the API — "interfaces deliberately
undesigned until bluehs teaches us what it wants"; the blessed
surfaces are small consumer-taught wrappers grown when consumers land;
the eventual component split (solver, Tcl, raw internals, simulation
control as separately-linked pieces) is that later milestone's
requirement, not v1's. Distribution manifests carry source commit,
schema, toolchain ABI, platform, and kernel-ABI pins (T2). The freeze
rule: freeze only what bluehs cannot add later. Scope boundary of
record: SVA is not deliverable through bluehs — it processes different
source. bluehs is also the stated successor direction for the
Tcl-based tooling lineage (the workstation UI having long been "a
stress test for bluetcl"), and the near-term driver is scripting the
compiler for emission tasks (lint waivers) that previously required
compiler round-trips.

**Typed simulation scripting** (PROPOSAL, evidence complete): a typed
second frontend over the same simulator-kernel seam the Tcl frontend
uses — not a replacement, pulled in by a concrete consumer. The
kernel ABI needs no additions for parity (it is strictly read-only;
the Tcl frontend has no write path either). Differentiators: typed
state decode through the recorded-types spine, property-based
stimulus via sidecar modules, invariant/coverage sidecars, and the
same interface driving trs artifacts unchanged (drop-in kernel ABI).
The first robust consumer is an isolated-worker lockstep differential
driver — in-process lockstep is not generally independent (shared
foreign state, stdio, RNG). Interactive poke/deposit is the ONE
candidate kernel extension, weighed separately because it costs
freeze surface in two engines; a synchronous stepping API (inline
single-step without the helper thread) exists as a candidate kernel
addition with model fuzzing as its consumer — kernel-ABI evolution is
coordinated across all its stakeholders before anything freezes (08).

## 2. The language server

Architecture (DECISION): two layers — an error-tolerant parser (new
code, differential-parse-tested against an identity corpus, promoted
to normative only on receipts) plus bsc-as-library semantics off
last-good artifacts. The operative design:

- **Path-indexed ranges outside CSyntax.** Ranges never go onto the
  core syntax type: the blast radius would be the whole typechecker,
  and CSyntax is a *derived* artifact for the BSV front end, so any
  annotation scheme must live outside it regardless. The parser
  produces the tree plus a path→range map; the typechecker reports
  errors by path (it recurses on the tree, so tracking is trivial);
  comments become path-keyed annotations the same way (the docstring
  map). T8 applied to diagnostics.
- **Parser modernization is the foundational step**: both parsers
  rebuilt on a modern combinator library with source ranges,
  multi-error recovery, and better messages — bolting recovery onto
  the existing parsers was tried and made errors worse; neither old
  library is worth reusing. One open implementation choice under the
  settled decision: a table-driven LALR(1) port is judged practical
  (layout moves to a lexer-side stack; error recovery nearly free)
  and sits beside the chosen combinator route (08). Shared step zero
  for docstrings, hover docs, and any formatter: **comments must
  survive lexing** — both current lexers discard them. A measured
  modern lexer (token-identical, byte-identical compiler rebuilds,
  large speedups on lexing-bound workloads) is the substrate either
  parser path builds on.
- **Definition-level granularity; incremental parsing rejected.**
  Files are small, parsing is fast, full-document sync suffices, and
  mandatory top-level type signatures mean every definition
  typechecks independently — parse-error poison pills mirror the
  existing type-error mechanism, composing recovery with partial
  compilation.
- **Interface files are the metadata home**: resurrected
  signature-level artifacts (much lighter than full implementation
  artifacts; the same design serves a fast type-check-only mode)
  carry ranges and docstrings; range reporting also enters the main
  compiler flow.
- **Feature scope by consumer reality**: hover with type + docstring
  (including as-declared vs normalized display), go-to-definition,
  references, and type holes are the core; textual completions and
  renames are deprioritized *because LLM agents cover them* — agents
  are a first-class LSP consumer class in their own right;
  waves-to-source navigation is adjacent UI space, not LSP proper
  (§3). Multi-location diagnostics are protocol-verified (the
  typeclass position-universe case); byte-based position encoding is
  negotiated explicitly. Type-at-use-site remains the canonical
  example of what compiler integration buys over a syntax-only
  server.
- **Touch-point tracing from generated Verilog back to source** —
  registers, instantiations, ports, rule predicates — is the named
  most-impactful feature: the compiler knows the information and has
  simply never had an interface to expose it. Source-to-RTL
  provenance is a many-to-many DAG, never one selected position.
- **Build integration inverts**: the LSP extracts the build graph and
  drives itself from it — it never generates build files.
- **Editor portability**: a portable baseline on language-agnostic
  features; editor-specific extras allowed where they genuinely pay;
  no environment left out.

Semantic authority is a versioned, action-keyed protocol: every reply
binds workspace/config, document version and buffer digest, snapshot
and transitive action identity, and classifies itself Exact /
StaleLastGood / Pending / Unavailable; stale semantics may display but
never silently drive refactors. The long-running worker cannot inherit
process-global compiler state — disposable workers keyed by action
generation first; session reuse arrives with the session architecture
(01 §3). The rust-analyzer precedent governs status: a non-official
parser against the reference compiler is standard sequencing, and
promotion is receipts-gated (an incremental-edit trace corpus — parser
behavior on transient broken buffers — is the stronger gate).

## 3. Typed observability

One artifact serves every consumer: generated **decoding functions**
(not static type tables — encodings can be custom), total over
4-state input, X/Z propagation defined per decoder kind, keyed by
type + resolved encoding evidence + codebook fingerprint + compiler
schema (02 §3), delivered in-artifact or as sidecars.

- **The type sidecar**: the compiler emits a companion file mapping
  dumped signals to source types (enums by constructor, tagged
  unions, structs); a viewer-side translator consumes it, making the
  wave *format* irrelevant to decoding. Container ruling: FST over
  VCD — FST's scope records carry a type slot that VCD simply lacks
  (a comment convention was rejected as a hack around a format gap);
  proprietary formats are reached by conversion until direct reads
  are worth their licensing entanglements.
- **Wave-to-source needs no viewer fork**: the open viewer speaks a
  small JSON control protocol with a go-to-declaration event carrying
  the signal's full hierarchical path; the tool-side work is a
  protocol client plus a path→source map from compiler position info
  — and one editor-side client can serve the open viewer and the
  commercial one (whose scripting layer plausibly speaks the same
  protocol — unverified). The compiler-side piece is shared across all routes.
- **The position-tracking doctrine** (Ravi): coverage display (05 §6)
  and wave-to-source both want better position propagation through
  the evaluator; state-element positions are already good — the
  shared investment is positions for *intermediate* signals: one
  substrate, two named consumers.
- **The agent-consumer reframing**: a quality capture of state and
  events plus a command-line probe tool can beat a human waveform
  viewer for debugging throughput — and the signals worth capturing
  typed are exactly the state elements and ports (everything else is
  a function of state; record state + fire events, not full
  evaluation). This reframes the decoder witness's first consumer as
  possibly a probe tool rather than a viewer, without changing the
  artifact.
- Human-readable shadow: emit source-language-typed comments on
  generated ports, registers, and wires — kept consistent with the
  decoder witness, never independent.

Dump policy: the waveform signal set follows the reference simulator;
typed dumping is the recorded aspiration; dump throughput has a named
direction (write-time dirty sets, then an AOT-emitted specialized dump
walk) behind a benchmark tripwire; wave generation supports multiple
dump formats by user configuration through one format-agnostic sink.

## 4. One query surface

From the library rung of the artifact graph onward, the engine lives
in the library: bluetcl, bluehs, the LSP, and the test orchestrator
consume the same memoized, snapshot-keyed query surface over artifact
nodes; a stable worker/query protocol is the terminal node of the
whole program. The session architecture (01 §3) is its
precondition. Bluetcl neither grows nor deprecates: one
implementation, two frontends; the Tcl surface keeps the
interactive-shell half and the EDA-familiar syntax; the interactive
test corpus is the parity anchor.

## 5. Pointers

Mechanism and evidence: the LSP design lane (the joint-scoping record
and its reviews); the bluehs and sim-scripting lanes; the
surfer-integration and coverage documents; the lexer/parser
modernization records. Indexed in the KB; open design decisions in 08.

## 6. RESOLUTIONS and OPEN questions

- RESOLUTION: path-indexed ranges; definition granularity; interface
  files as the metadata home; receipts-gated parser promotion.
- RESOLUTION: the action-keyed semantic-authority protocol; no
  process-global state in long-running workers.
- RESOLUTION: one decoder witness for every observability consumer;
  FST-class containers carry the types; one protocol client can serve
  multiple viewers (commercial-viewer hooks unverified).
- OPEN: the parser implementation choice (combinator vs LALR) under
  the settled modernization decision.
- OPEN: how typeclass position universes and merged origins render
  for a touch point — the many-to-many provenance question (§2; 08).
- OPEN: poke/deposit and the synchronous stepping API — one
  coordinated kernel-ABI decision.
- OPEN: the docstring marker standard (comments-survive-lexing is
  step zero either way).
