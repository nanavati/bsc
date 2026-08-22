# CtxRed Retirement Plan (draft v0.1, 2026-08-22)

**What this is.** A staged plan to retire `cCtxReduceIO` — the package-wide, source-AST-mutating
context-reduction pass — while keeping every benefit it actually delivers. Grounded in
B-Lang-org/bsc `main @ 941eecf` (all 495 lines of `CtxRed.hs` and every external caller read for
this plan), the 2026-08-16 CtxRed-removal audit, and the 2026-08 design threads on visible type
application (VTA) and BA-derived exact contracts.

**Status: proposal for discussion.** Nothing here is ratified.

---

## 1. Why it dies, why it can't just be deleted

Two forcing functions and one constraint:

- **VTA needs stable telescopes.** CtxRed rewrites every signed definition's declared `CQType`
  (`CtxRed.hs:144-151` via `ctxRedCQType`, which runs `reducePredsAggressive` at `:420` and
  substitutes the result into the type and body). Solving can drop, alias, reorder, or
  substitute written binders; `Scheme` then derives the positional `@`-telescope from what
  survived, and the `.bo` signature serializes only the rewritten type. A written source slot
  can disappear, merge, or move — fatal for positional type application. (Audit, confirmed
  against source.)
- **The contracts design needs its boundary jobs relocated.** GenWrap floats flat-interface
  field types as free tyvars under `WrapField` constraints (`GenWrap.hs:907-921`) and relies on
  the package-wide pass (`CtxRed.hs:62-70` `instance CtxRed CField`, `:86-88` `Cstruct`) plus
  its own `cCtxReduceDef` call (`GenWrap.hs:538`) to solve them. The picked-strategy/ATF
  boundary design replaces this with pick-time ground solves — the package-wide pass becomes
  an obstacle, not a dependency.
- **Constraint: blind bypass is measured to be unacceptable.** The audit's benchmark: with all
  reducible predicates preserved and no internal canonicalization, N=32 provisos × M=100
  functions went from 1.65 s to >249 s (unfinished), and a producer `.bo` grew 52.2×. CtxRed's
  real value — dedup of identical constraint heads, FD improvement computed once, evidence
  shared instead of re-solved per use, and dictionary-ABI shrinkage from declaration-site
  discharge — must have named replacements before the pass dies. (Also measured: on real
  workloads the pass + its symtab rebuild is only ~0.23–0.24 s of 2.36–2.39 s on gh678, ~10%
  absolute — the wall-clock stakes are modest; the blowup risk is ABI size and re-solving at
  scale.)

**The organizing principle** (same pattern as the ATF cache and the contracts design):
*the written form is identity; solved facts are a cache.* The declared telescope is the public
API, the `@`-index, the serialized signature — never rewritten. The reduced/solved form lives in
internal, memoized, coherence-gated state (and, where the ABI needs it, behind an explicit
worker/wrapper adapter) — never in the source of truth. GHC precedent throughout: OutsideIn's
rigid Givens, `-Wredundant-constraints` instead of constraint deletion, inert sets, per-version
interface machinery.

---

## 2. Job inventory: everything CtxRed does today

Enumerated from source. Each job gets a named destination; the pass dies only when every row is
relocated.

| # | Job | Where | Destination |
|---|-----|-------|-------------|
| J1 | Rewrite declared `CQType` of every signed def; residual provisos become the dictionary ABI; subst applied into bodies | `CtxRed.hs:144-151`, core at `:377-455` | Split: identity → raw telescope (Phase 1); solving perf → evidence cache (Phase 2); ABI → worker/wrapper decision (Phase 3) |
| J2 | Solve GenWrap's floated flat-ifc field constraints (struct fields incl. defaults) | `CtxRed.hs:62-70, 86-88` | Pick-time ground solves per the contracts/ATF design (Phase 4; coordinates with the contracts proposal) |
| J3 | Class fields + default bodies | `CtxRed.hs:99-126` | Ordinary typecheck against raw signatures (Phase 4); watch VTA's class-default serialization (GenBin tag 43) |
| J4 | Instance-head normalization — `ctxRedInstHead`/`expTFun`, **conditional**: expanded head used only if expansion produced predicates; in-source XXX admits "existing code relies on the current behavior" | `CtxRed.hs:373-380, 396-409` | Heads retain written form; matching normalization moves to a separate solver/index view (PredTrie's `normT` already leaves `TIatf` in place); `MakeSymTab.hs:447` stays the head-legality authority (Phase 4) |
| J5 | Reduce local typed annotations (`CLamT`/`CHasType`/`CSBindT`) | `CtxRed.hs:161-171, 216-224, 280-287` | Narrow canonicalize-and-require-empty checker — validate, never rewrite (Phase 4) |
| J6 | Foreign decl types (`Cforeign`) | `CtxRed.hs:~95` | Same as J5 (Phase 4) |
| J7 | ATF resolution recording (side effect of `sat`), returned as `atfCacheFromCtxReduce` | `CtxRed.hs:34-47`; `bsc.hs:412` | Typecheck's own `tiATFCache` already records the same facts; verify cache-content parity without the pass (Phase 4) |
| J8 | Used-package tracking → unused-import warnings | `CtxRed.hs:47`; `bsc.hs:641` | `recordPackageUse` in the remaining TI runs (typecheck); warning-parity test (Phase 4). Audit: this is accounting policy, never a reason to rewrite signatures |
| J9 | Per-def reduction for boundary analysis: `cCtxReduceDef` in GenWrap (`getDef`, wrapper type) and GenFuncWrap (noinline) | `GenWrap.hs:538`, `GenFuncWrap.hs:97` | The pick-time ground-solve helper (single `matchTop` + fd projection at ground inputs; Phase 4, with the contracts work) |
| J10 | The post-elaboration wrapper re-typecheck's own CtxRed run | `bsc.hs:2201` (inside `compileCDefToIDef`) | Dies with the contracts proposal's continuation removal — no work needed here beyond sequencing |

**Downstream consumers of the reduced form** (these are what each phase must re-point):
`Scheme`/`quantifySpecified` (the `@`-telescope — the VTA conflict); `genUserSign`/
`genEverythingSign` (`.bo` signatures, `bsc.hs:635-637`); the typechecker's view of declared
Givens and the executable dictionary ABI; GenWrap's flat-ifc types; the merged ATF cache
threaded into elaboration; the unused-import check.

---

## 3. Phases

Each phase is independently landable, differential-tested, and gated. Order matters: the
canonicalizer (Phase 2) must exist before anything widens raw contexts, or the audit's measured
blowup recurs.

### Phase 0 — Census and fences (no behavior change)

- Wire the existing `DFctxreduce` dump (`Flags.hs:208`) into a **telescope-drift census**: for
  every def in a corpus (testsuite + bsc-contrib + internal designs), record whether CtxRed
  changed its telescope's shape (solved away / aliased / substituted / reordered) and its
  predicate count delta. This quantifies both VTA's exposure and the ABI win Phase 3 must
  preserve.
- Stand up the perf fence: the audit's synthetic N×M benchmark, gh678, full-testsuite wall
  time, and `.bo` size tracking. All later phases gate on it.
- Instance-head census for J4: every `Cinstance` head whose `expTFun` expansion is *used*
  (the conditional arm), since those are the heads whose meaning could shift.
- Acceptance census: programs that typecheck **only because** CtxRed reduced something early
  (run the testsuite with the pass's output discarded-but-checked to find them).

**Exit:** censuses published; fences green on baseline; no compiler change shipped.

### Phase 1 — Identity split: raw telescopes become the API, signature, and `@`-index

- `Scheme` derives specified binders from the **pre-reduction** written `CQType`; signatures
  serialize the raw form. (This is the VTA-unblocking change; it overlaps the VTA branch's
  `Specified`/`Generalized` work and should land with or immediately before it.)
- CtxRed keeps running, but its output loses authority over API/signature/telescope — it feeds
  only the typechecker's internal state and, transitionally, the executable ABI.
- Because signature (raw) and ABI (still reduced) now differ, record the mapping explicitly:
  a per-def **ABI adapter annex** in the `.bo` (same annex pattern as `ipkg_atf_cache`,
  `ISyntax.hs:136-144`). This is the contained, temporary "weird" — explicit and serialized,
  never a silent rewrite. Phase 3 replaces or deletes it.
- Bonus effect to verify and then rely on: raw signatures are insensitive to instance-
  environment changes (what reduces today depends on what's imported), so `.bo` signature
  stability — and everything keyed on it, including future contract digests — improves.

**Exit:** VTA's FD-target tests pass locally and through separately compiled `.bo`s; byte-level
signature parity for all defs the Phase 0 census marked telescope-stable; adapter annex
round-trips; `.bo` tag bump coordinated (see §5).

### Phase 2 — Internal canonicalizer + evidence cache

- Build the indexed evidence environment the audit specified: canonicalize instantiated
  Givens/Wanteds, deduplicate identical heads, apply FD improvements once, reuse solved
  evidence across uses. Template: the ATF cache — coherent-only recording (`TCMisc.hs:223-241`
  T0158 policy; the incoherent path already refuses to record, `TCMisc.hs:400-406`),
  per-package ownership in the `.bo`, explicit merge rules.
- Replace `joinNeededCtxs`'s pair-at-a-time quadratic merging (audit perf note) as part of the
  same work.
- Persist a solved-evidence annex beside `ipkg_atf_cache` so importers reuse rather than
  re-solve.

**Exit:** the N=32/N=128 synthetic benchmark with raw contexts preserved internally lands
within ~1× of today's baseline (this is the gate that proves blind-bypass costs are gone);
gh678 within noise; full-testsuite fence green.

### Phase 3 — The dictionary-ABI decision

- With Phase 2 in place, re-measure: does declaration-site discharge still buy meaningful `.bo`
  size / call-site cost? (Phase 0's census says how many defs it even affects.)
- **If yes:** worker/wrapper — exported wrapper at the declared type (API, signature,
  telescope), internal worker at the reduced type, wrapper inlinable, adapter explicit. This is
  the principled home of Phase 1's annex, and it shares machinery and review bandwidth with
  the #925 dictionary-lifting/sharing work — land them as one arc.
- **If no:** ABI = raw telescope; delete the Phase 1 adapter annex outright.

**Exit:** cross-package link-level differential tests (mixed old/new callers impossible by tag,
but mixed w/w and non-w/w defs within one build must interoperate); perf fence green; a
one-page record of which option was taken and the measurements that decided it.

### Phase 4 — Retire the targeted reducers, job by job

Kill list, each with its own parity test (see inventory for destinations):
J2/J9 → pick-time ground solves (with the contracts work; GenWrap stops floating constraints);
J4 → written instance heads + solver-side index view, delete the conditional `expTFun` rewrite
(gated on the Phase 0 head census — any head whose meaning shifts is a loud error with
migration guidance, not a silent change); J5/J6 → require-empty annotation checker;
J3 → ordinary typecheck of defaults; J7 → ATF-cache content parity without CtxRed's
contribution; J8 → `recordPackageUse` in typecheck + unused-import warning parity.

**Exit:** every row of the inventory relocated with its parity test green; `cCtxReduceIO` is
dead code guarded by a flag.

### Phase 5 — Delete

- Remove `cCtxReduceIO`, its `bsc.hs:412` call, and the post-CtxRed symtab rebuild
  (`bsc.hs:415-419`) — the measured ~10% gh678 win arrives here for free.
- Remove `cCtxReduceDef` once GenWrap/GenFuncWrap are on the ground-solve helper.

**Exit:** full testsuite parity; all fences green; VTA suite green; contracts differential
(if landed) green; `CtxRed.hs` reduced to whatever pure helpers the index view kept, or gone.

---

## 4. Risk register

- **R1 — Conditional instance-head normalization** (`CtxRed.hs:396-409`): the in-source XXX
  says existing code relies on the use-expansion-only-if-nonempty behavior. Phase 0's census
  is the mitigation; any behavior change ships as a diagnostic, not a silent shift.
- **R2 — The incoherence split is unexplained in-source**: CtxRed runs `runTI flags False`
  ("incoherent instances should not be matched at this time... XXX why?", `CtxRed.hs:40-41,
  52-53`) while typecheck runs with incoherent matching per flags. Moving work between the
  passes changes *when* incoherent matching is attempted. This archaeology item must be
  resolved (documented, then tested) before Phase 4 moves J2-J6.
- **R3 — Order-sensitive resolution bugs**: `reducePredsAggressive'` deliberately avoids the
  sorting optimization because "there are some existing bugs where the order in which preds
  are reduced affects whether instance resolution succeeds" (in-source comment citing
  bsc-contrib GenCMsg.bs). Consolidating solver entry points can flip such programs either
  way. The acceptance census (Phase 0) plus a pinned corpus of known order-sensitive cases is
  the fence.
- **R4 — Acceptance drift**: programs that only typecheck because early reduction happened
  (or that fail with different, worse errors when residuals survive longer). Census +
  error-message goldens.
- **R5 — Format-tag contention**: Phases 1 and 2 add `.bo` annexes (adapter, evidence cache) —
  the same coordination problem as VTA (bsc-bo-20260815-1/tag 43), the pattern-match stack,
  and the contracts work. Annexes should be self-versioned optional sections; sequence the tag
  bumps explicitly across the four efforts.

---

## 5. Coordination map

- **VTA**: Phase 1 *is* the audit's landing precondition ("not architecturally ready to land
  until source quantifier telescopes are made independent of package-wide context reduction").
  Land Phase 1 with the VTA branch or immediately before it.
- **Contracts proposal**: Phase 4's J2/J9/J10 are the same work as the contracts design's
  pick-time boundary derivation (strategy-indexed `Wrap c a`, `Boundary` as an ATF,
  solve-no-search evaluation); J10 dies with the continuation. Neither effort should build the
  ground-solve helper twice.
- **#925 dictionary lifting/sharing**: Phase 3's worker/wrapper option is the same machinery;
  one review arc, and the org's stated typechecker-perf priority pays for it.
- **ATF cache line**: the coherent-only + per-package-ownership discipline just landed at HEAD
  is the template for the Phase 2 evidence cache and the Phase 1 adapter annex.

## 6. What stays forever

Constraint solving itself (`sat`/`reducePred` in the typechecker), the ATF solve-no-search
machinery, coherence enforcement (T0158), and the raw written telescope as the single source of
identity. What dies is one thing only: the package-wide pass's authority to rewrite declared
types — and then the pass itself.
