# 10 — The Meeting Record: Bluespec Decisions Outside the KB

What the meeting corpus (Gemini notes for the Bluespec meetings and the
compiler-team 1:1s, March–August 2026, plus the Bluespec Drive folder)
adds to the KB-derived picture of **Bluespec-the-language-and-compiler**.
The KB captures the design lanes; this document captures the decision
timeline, the ecosystem machinery around the lanes, and meeting-sourced
facts the KB never recorded. Where a meeting fact grounds or corrects a
design document, that document cites it. Deployment-side and
company-internal material from the same meetings lives exclusively in 07,
per the doc-set rule that 07 is the only home for such specifics.

**Status:** v1.1 — 2026-08-24 (Claude, meeting-notes crawl). Labels as
elsewhere. Sourcing: Gemini auto-summaries (may contain errors) except
the compiler tour, which is a full transcript.

## 1. The open-source Bluespec sync timeline (biweekly, with upstream)

- **May 15**: output port splitting adopted as the standard solution for
  interface symmetry.
- **May 29**: PR 939 (heap-cell naming); parser layout-error heuristics;
  computed rule names; EBNF parser documentation.
- **Jun 12**: DECISION — Cabal migration prioritized (developer tooling +
  HLS); upstreamable-cleanup line; type-based search utility (a Bluespec
  Hoogle) local-first; GHC 8.8 support request honored.
- **Jun 26**: DECISION — no-split default for vectors (performance); new
  types as the explicit split mechanism; release slips to August;
  PRs 924/940.
- **Jul 10**: DECISION — ShallowSplit is the recommended user surface;
  port-splitting parts 2+3 merge as experimental-with-caveats;
  deriving-via documentation.
- **Jul 24**: lint-noise elimination in generated Verilog without extra
  flags; constant folding of reset values; a Yosys-based flow discussed;
  port splitting paused; internal type-handling performance.
- **Aug 7**: LSP development discussed; external code-review funding
  committed; upstream semantic-analysis draft PR; compiler-internals
  presentation to be shared; academic teaching materials open-sourced.
- **Aug 21 ("bsc as smaller tools")**: DECISION — adopt a **3-phase
  compile split into modular executables** (reduce accidental coupling,
  improve parallelism and integration with external build systems);
  **contract files** for dependency management and cache efficiency;
  Cabal for native build tasks plus standard Makefiles; GHC default
  bumped to the GHCup-recommended version; a stdlib package maintainer
  named, owning a build-integration guide; a Nix-driver × Cabal
  investigation; action to circulate a 3-phase compile-flow proposal.
  This resolves the KB's recorded gap: the smaller-tools doctrine's
  origin is now on the record. The 3-phase split, contract files, and
  the artifact-graph program's manifests (01 §2) are one convergence:
  contract files are the manifest program arriving from the
  build-integration side (RESOLUTION: design them as one artifact
  family, not two).

## 2. The upstream engagement program

- **PR landscape review (Aug 5)**: the 67–80-PR fork backlog was
  categorized into five workstreams; quick wins self-assigned first,
  then per-workstream design sessions. DECISION: a successful internal
  review means "builds pass tests and ready for upstream submission";
  performance metrics go into PR descriptions. A **contract with
  Bluespec, Inc. for an upstream-review SLA** is to be drafted (07
  §4.4's program); the missing documentation of which upstream PRs rode
  the previous release gets recreated.
- Upstream delay is managed by transparent tracking, not pressure; the
  standing priority is **preventing forks by engaging volunteers**
  (Aug 3).
- Pre-history (Mar 27): retroactive payment for upstream PR-review
  effort; a PR-reviewer role specification — the review-bandwidth
  problem was recognized before the Bluespec, Inc. program existed.
- Stacked PRs adopted to decompose large branches into upstream-ready
  reviews (Aug 3); the in-flight integration branch gets decomposed
  into candidate upstream PRs.

## 3. The LSP arc and the Unison engagement

- **Mar 20**: the strategic frame — LLM assistance made an LSP and
  parser refactors "feasible and bounded"; the named missing piece for
  Bluespec-at-scale: a fast hardware-quality feedback loop
  (Yosys/OpenROAD cell, timing, power), because "powerful Bluespec can
  easily lead to terrible hardware."
- **Mar 27**: the current AI-coded LSP "reliably performs 90% of its
  functions" but needs polish, a common parser, and proper packaging of
  bsc as a library.
- **May 14/15**: LSP declared essential for maintainability; external
  engagement evaluated; GHCi integration proposed (load compiler modules
  into GHCi for scripting and metadata extraction) — the origin of
  bluehs; incremental-update requirements to be investigated before
  committing.
- **Aug 4 (compiler tour, full transcript)**: architectural narration
  for Unison (Paul Chiusano, Dan Doel) — technical content folded into
  01–06 and §5 below. The .bo-files-for-LSP exchange concludes: .bo
  carries most of what a background indexer needs (I-syntax with source
  positions, per-package signature files; symbol table reconstructible
  from the transitive closure) but not source text, and an interactive
  path is needed for mid-edit, non-typechecking states.
- **Aug 7 (LSP meeting)**: DECISIONS of record — path-based range
  indexing decoupled from the primary syntax tree (avoids disruptive
  syntax modifications); parser modernization on Megaparsec with error
  recovery and multi-error reporting (Dan Doel); essential-features-
  first scope (stable navigation, type checking); **resurrect interface
  files as the persistent home for auxiliary metadata** (doc strings);
  manage LSP's byte-based position encoding explicitly. Unison to send
  a proposal (rates, scope, weekly status meeting, shared Slack); a
  Cabalize-build PR planned.

## 4. The longer-horizon project set (Drive, Apr 2026 — Ravi's document)

Four named projects "beyond anyone's current roadmap", each with a
delivery model:

1. **Compiler-integrated LSP** replacing the AI-coded one; uses bsc's
   own parser and typechecker so it stays correct as the language
   evolves; requires (at least partial) cabalization — which a margin
   note says is separately valuable on its own. Contractor-friendly
   (the Unison engagement is this project starting).
2. **Full SystemVerilog output mode** (umbrella; pieces independent):
   SV-type integration (absorb the external type-emission tooling into
   the compiler, keeping user-implementable typeclasses for genuinely
   extensible parts); newer constructs — always_ff, always_comb, logic,
   unique/priority case, where **unique case propagates bsc's
   exhaustive-and-exclusive-by-construction knowledge to downstream
   tools that would otherwise reprove or miss it**; SV assertion
   emission (some generatable without source-level assertions;
   source-level ones better); native SV import (the current import
   mechanism was designed for Verilog). Needs internal capacity.
3. **Reorganize scheduling around user-specified schedules** — "the
   biggest by a wide margin"; the compiler checks a stated schedule
   rather than inferring one; margin note: compatibility of the stated
   schedules must still be *checked*. A secondary payoff: **interface
   arguments** (dropped historically because the compiler couldn't
   capture their scheduling) get unblocked. Research-shaped: direction
   settled, shape open. This is the polymorphic-scheduling RFC's
   schedules-as-values thesis (03) independently stated as long-horizon
   strategy — the two documents should cite each other (RESOLUTION:
   recorded in 03).
4. **Redo Verilog module imports** from scratch on top of SplitPorts
   (the BVI design predates it); restore computed module names (the old
   "module verilog" feature); margin note extends this to computable
   port names (pVeriPort in CParser.hs is a string literal today) —
   "generally anything with string literals." Folded into 02 §4's BVI
   family as the long-horizon fifth program.

## 5. Compiler-internals facts first recorded in meetings

Folded into the area documents with citations; consolidated here:

- **Architecture of record (tour)**: whole-program optimizing compiler,
  term-rewriting based; CSyntax → ISyntax → ASyntax; two parsers
  converging on one AST (BSV parses imperative-style then desugars to
  repeated let-bindings; classic parses directly); typecheck phase
  bundles symbol tables, deriving, and the two wrapper passes
  (null-inline and synthesized-module); post-elaboration the compiled
  module's .bo carries an import-shell with full scheduling annotations
  (as if imported Verilog) rather than the code; ASTATE is the
  rules→wires phase change (mux vs priority mux by mutual exclusivity).
- **Optimization-placement doctrine (tour)**: bsc must own (1)
  optimizations that can affect scheduling — schedule conditions are
  arbitrary boolean predicates — and (2) pack∘unpack→identity; most
  everything else properly belongs to downstream tools. ASyntax
  optimizations were historically removed because synthesis tools
  already did them.
- **Wrapper dictionary flow-through defect (tour)**: "most of the pain
  in wrapper generation is reconstructing the big dictionaries used for
  the wrappers, which is utterly silly because the first type check
  already did that and you should just look it up — we do not flow that
  properly." And the **deriving-after-genwrap ordering defect**: wrapper
  generation cannot use the full universe of instances because deriving
  runs after it (04 §6).
- **CtxRed's stated purpose (tour)**: derived Bits instances carry many
  constraints; ctxreduce reduces them once rather than having the
  typechecker re-solve repeatedly (the retirement plan of 04 §3 replaces
  this rationale with caches).
- **The WrapField regression and the strictness program** (performance-
  assessment engagement, Sep 2025): Hyper predates NFData and its
  replacement (#811) is worth ~13% alone; the compile-time regression
  root cause is WrapField's String field-name type argument defeating
  context joining (joinNeededCtxs) so identical dictionaries are
  constructed once per blasted vector element; three candidate fixes
  are on record (drop the element index from field names; join after
  reduction to WrapMethod; CSE generated dictionary code, precedent
  simplifyDictBindings); and the surgical strictness proposal — ISyntax
  strict in everything except ICon's IConInfo, because eSubst never
  substitutes into ICon while laziness must survive for
  ICDef/ICValue/IClock/IReset/IInout/ILazyArray knots (04 §6).
- **Interning enables dictionary lifting** (Aug 13): strictness
  annotations plus ground-type interning are sequenced specifically to
  make dictionary lifting sound and fast; independently, the
  dictionary-lifting fix is flagged as the release-blocking soundness
  item (Aug 17) — matching the KB's lift-dictionaries hold (04 §2).
- **Union-find typechecker architecture** proposed (Aug 6) with "purity
  essential for tooling compatibility" and a systematic invariant-
  checking policy to be agreed with upstream. SUPERSEDED (Ravi,
  2026-08-24): the proposal did not pan out — most type variables are
  dropped quickly and do not form alias chains that union-find would
  help (04 §4).
- **Pattern-match exhaustiveness checking deferred** pending testing
  and a rebase onto recent upstream (Aug 13); the implementation "fails
  specific hardware values" and needs a standalone test approach;
  synthesizability of checked constructs is a hard requirement (Aug 3).
  Recorded as a status correction in 04 §5.
- **Scheduling quadratic + the resources/uses patch (tour)**: scheduling
  considers every rule pair; an experimental patch reworks it in terms
  of resources and uses — same schedules, often much faster, "doesn't do
  some of the nastier things" (03 §3).
- **Numeric solving (tour)**: two-level today (handcrafted simplifying
  instances, then SMT thumbs-up/down); the stated wish is an engine
  that *learns* (knows a+a=2a; cannot conclude a+2a=3a) — motivating
  04 §3's numeric-engine exploration. Numeric kinds are naturals by
  design ("no negatives — important in lots of numeric reasoning").
- **Higher-rank types via GADT-style reasoning** expected to be
  unblocked by a fundep-improvement fix (Mar 27) — a wishlist item no
  KB lane carries; consistent with 00 §3's front-end growth direction.
- **The unsized-bit-literal wishlist** (Mar 27) is the recorded origin
  of the '0/'1 classic-literals compat feature (04 §5).
- **Parser posture (tour)**: two old parsers, different libraries,
  neither reusable for a rewrite; wants = multiple parse errors, better
  messages (classic's "expected token" errors especially), error
  highlighting; classic-only shadowing/unused warnings (BSV can't —
  imperative shadowing is idiomatic); a "secret door" embeds classic
  code inside BSV files (works historically, maintenance status
  unknown). The LSP meeting's Megaparsec decision (§3) is the answer.
- **bluetcl/BDW (tour)**: the bluetcl interpreter now accepts both
  classic and BSV syntax; makefile generation via a bluetcl script is
  the parallel-build workaround (bsc never builds in parallel natively);
  BDW is "a stress test for bluetcl"; the in-repo Emacs modes don't
  work. The bluehs program (06 §1) is the stated replacement direction:
  "who needs an API — access to all of BSC's libraries in Haskell,
  settle to a sensible API later"; near-term driver is lint-waiver
  emission scripting.
- **Waveform↔source mapping (tour)**: the desired Verdi-class feature,
  targeted at the open-source Surfer viewer (chosen because it
  decomposes structs and tagged unions properly) — the same direction as
  06 §3's typed-observability program.
- **Conflict-annotation enforcement (tour)**: a recent fix makes bsc
  actually check scheduling annotations when a compiled module is
  instantiated in a foreign Verilog design.
- **A user-feature survey** of the broader Bluespec community is
  planned, plus release of the Haskell scripting for outside
  experimentation.

## 6. The ramp project menu (Drive, Jul 2026 — generic compiler items)

A curated breadth-first menu for new compiler-team members; the
Bluespec-general items double as a small-projects inventory:

- **First-class ===**: today an operator on Bit n only; generic
  emulation cannot reach the tag tests inside tagged unions; open design
  question — Eq-class method vs dedicated built-in. A general Bluespec
  improvement.
- **TypeError typeclass** (upstream #286): GHC-analogous custom
  typeclass errors via a ContextErrors filter — targeted, user-friendly
  missing-instance messages.
- **Bluespec-type comments on generated ports/registers/wires**: the
  compiler knows the types (bluetcl exposes them); emit them as comments
  in the generated Verilog, with comment syntax following the source
  module's language (BH vs BSV).
- **Bluesim C++ handoff to the build system**: bsc emits Bluesim C++
  incrementally and lets the outer build system compile/cache it,
  instead of compiling and linking at final-link time itself (upstream
  #455, #10837, #44 for context).
- Documentation projects: release-cutting runbook; a systematic
  user-issue intake pipeline (named as a design gap).
- Areas deliberately excluded as ramp material (a useful map of where
  accumulated, undocumented semantic weight lives): the scheduler
  (though scheduler *error messages* would be a good bounded project),
  IConv/AConv, ITransform/AOpt ("heuristics whose operational knowledge
  isn't captured in code or docs"), with wrapper generation named as the
  ramp *destination* — exactly the typecheck/genwrap/typeclass nexus
  that 04 identifies as the front end's center of gravity.

The menu's deployment-specific items, and the teaching-strategy
curriculum, are recorded in 07.

## 7. Access gaps this crawl could not close (NEEDS-RAVI)

1. The **coverage proposal** document: referenced in meeting actions,
   not findable by the agent service identity (ai.agents@matx.com) in
   Drive. Share it (or name its location) and it gets folded into 05.
2. **Full Gemini meeting notes/transcripts** (beyond the compiler tour)
   are restricted; only the summary emails were readable. Sharing the
   meeting-notes Drive folder with ai.agents@matx.com would let future
   crawls read the Details sections, which are materially richer than
   the summaries.
3. No auto-notes exist for the **Jul 22 roadmap/ramp meeting** or the
   **May 13 "Formal Bluespec" meeting** — if they carried decisions
   worth keeping, they need manual capture.

## 8. Lane pointers

Sources: the compiler-tour transcript; the Bluespec Drive folder
(Longer-Horizon Bluespec Projects; Bluespec Compiler Ramp Project Menu;
Bluespec Teaching Strategy; Bluespec performance assessment notes);
Gemini summaries for the eight open-source syncs, the LSP meeting, the
PR landscape review, and the compiler-team 1:1 series. Deployment-side
extracts from the same corpus: 07 §6. The KB deposit for this review
registers this document as the meeting-record index.
