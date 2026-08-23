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

**The validity criterion** (Ravi, 2026-08-22): early context reduction is meaning-preserving
only when the instance match is **coherent and closed**. Coherent: every scope would select the
same instance — committing early on an incoherent match is a semantic choice made in the wrong
scope, which is why CtxRed already runs with incoherent matching disabled (`runTI flags False`,
`CtxRed.hs:40-41`; the in-source "XXX why?" has this as its answer). Closed, in two dimensions:
*type-closed* — no pending instantiation can redirect the match, which BSC actively tracks
(`MatchResult = NoConclusion | Fails | Matches`, `byInstIsReducible`/`matchTopIsReducible`,
`TCMisc.hs:1715-1740`); and *world-closed* — no future instance can redirect it, which BSC
**assumes but never checks**: the reduced signature bakes in the defining package's instance
world, and a downstream more-specific overlapping instance silently re-opens a frozen choice.
The only world-closed classes in the tree are the StdPrel computed ones — instances constructed
by `genInsts` functions, `allowIncoherent = Just False` (`StdPrel.hs:78-93`) — instance-as-
total-function is closedness by construction, and it is exactly where discharge is safest and
most profitable. **Recursive instances pin the commitment tiering** (2026-08-22): an instance
body's own wanted at a non-ground head (`Eq (List a)` inside `instance (Eq a) => Eq (List a)`)
is discharged today by committing at a variable head — the knot itself is `sat`'s machinery
(`TCMisc.hs:343` "tie the recursive knot", `isSelfRec` `:709`), untouched by retirement, but a
blanket never-commit-at-non-ground rule would force the self-constraint into the context —
which is exactly where Deriving already puts it: `doDEq` emits the naive field-derived context
verbatim (`Eq (List a)` inside its own instance, cross-reference chains for mutually recursive
families; `Deriving.hs:275`), and it is CtxRed that erases it today. The body-side knot and the
declared-context cleanup are therefore two separate jobs: the tiering here covers the first;
J11/§3.5 owns the second. So
the rule is per-class: (a) declared-open classes always defer; (b) ordinary classes commit at
non-ground heads when the unify-guard is clean — exactly current behavior, zero migration,
residual exposure identical to today's; (c) the sound long-term footing is Haskell's own
argument — with no-overlap as the default (overlap only by explicit declaration), every
ordinary head is world-closed by construction, upgrading (b) from status-quo-sound to sound.
The open/overridable marker thus serves discharge admission, sacrificial-instance retirement,
catch-all deferral, and recursive-instance commitment. Three regimes follow: (i) coherent ∧ closed → early reduction is a pure
optimization, valid anywhere (the only regime P3 discharge and unrestricted evidence reuse may
operate in); (ii) coherent ∧ open-world → valid only relative to a pinned environment — cached
with the environment stamped on it, or deliberately frozen at a boundary (the contracts
design's resolve-once-in-defining-environment manufactures closedness by snapshot); (iii)
incoherent → never reduce early; defer to the use site, as `runTI False` already does. This
also accounts for CtxRed sometimes *enlarging* predicate counts: aggressive reduction in the
open/unground regime trades one pred for an instance context it cannot discharge.

**The in-tree witness** is `SplitPorts` (`Prelude.bs:4885-4887`): *"XXX if the default instance
is the only one, then it gets inlined in CtxReduce and other instances for this class are
ignored"* — written directly above `instance SplitPorts () ()`, which exists (in part) as a
**sacrificial sibling instance** whose structural job is to block that inlining. Mechanism: a
class designed as catch-all-plus-user-overrides is *deliberately world-open*; with only the
catch-all in scope, its context-free head force-matches even a variable-headed constraint, and
CtxRed discharges `SplitPorts t p ↦ p := Port t` into the reduced type — downstream overrides
are silently ignored. The reducer evidently does defer when a second in-scope instance unifies
at a variable head (that is why the hack works: the `()` instance is the unifying sibling), but
that in-scope guard is only the shadow of world-closedness — it cannot see instances that do
not exist yet, and a sole-catch-all class sails past it. Corollary: GHC-style overlap pragmas
alone cannot fix this (the sole-instance case has no sibling to trigger any overlap rule); only
the never-commit-at-non-ground-heads rule for open classes does.

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
| J11 | Shrink derived-instance contexts: Deriving emits naive field-derived contexts — recursive self-preds (`Eq (List a)` in its own instance), mutual-recursion cross-references, duplicates — and free-rides on the pass to reduce them to tyvar-headed form | `Deriving.hs:275` (`doDEq`; the other `doD*` alike) feeding the J1 core | Generator-owned context inference (§3.5, jurisdiction bullet): re-scope the reducer core to derived instances only — no written telescope exists there, so the no-rewriting rule is not engaged; H98 §10 / GHC `simplifyDeriv` precedent makes the fixpoint the *definition* of the derived context, not an optimization |

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
- **Provenance split**: attribute predicate counts and solver time to user-written vs
  Deriving-generated vs GenWrap-generated definitions. This decides how much the companion lane
  (§3.5) buys; expectation to test: generated code dominates predicate traffic in typical
  packages.
- **Regime census** (per the §1 validity criterion): classify every constraint CtxRed discharges
  in the wild as (a) computed-class head (StdPrel `genInsts` — world-closed, safe), (b) single
  total instance NOT intended for override (safe in practice, world-open in principle),
  (c) **overridable-by-design** — a universal catch-all the class expects users to override
  (`SplitPorts`, the `WrapField`→`WrapMethod` delegation, and any library class of that shape):
  regime (ii)/(iii), must never discharge at non-ground heads — note today's detector for this
  intent is *accidental* (instance count, per the §1 witness), or (d) other. Expectation to
  test: (a)+(b) dominate, meaning the ABI win survives the criterion nearly intact.

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

### §3.5 Companion lane (with Phase 1): born-reduced generated code

The no-rewriting rule protects *written* telescopes; generated code has none — its declared
types are the generator's choice, so the generator may (and should) discharge constraints at
emission time. Generation runs in the defining package's environment, at ground heads, and for
width arithmetic against the closed computed classes: it is a pick-time solver in exactly the
right regime. Today it emits the opposite: `doDEq` builds contexts with duplicate preds and
preds at concrete types (`Deriving.hs:272-275` — the identical heads `joinNeededCtxs` merges
quadratically), and `doDBits` manufactures fresh tyvars and `Bits`/`Add`/`Max` proviso chains
even for fully monomorphic types (`Deriving.hs:440-510`), leaving CtxRed/typecheck to solve
puzzles the generator could have not posed.

- **Mechanism — defer, don't solve (Ravi, 2026-08-22).** The generator cannot use the
  typechecker: at derive time the symtab and the generator's own sibling instances do not exist
  yet. It does not need to. `SizeOf` — already the ATF of `Bits` in the Prelude
  (`class coherent Bits a n | a -> n where type SizeOf a = n`, `Prelude.bs:403-404`) — plus the
  numeric type functions (`TAdd`/`TLog`/`TMax`/..., `PreIds.hs:84-91`) form a vocabulary for
  **answers the generator cannot compute yet**: emit the width as a closed-form deferred
  expression (`TAdd (TLog …) (TMax (SizeOf A) (SizeOf B))`) instead of fresh tyvars constrained
  by `Bits`/`Add`/`Max` proviso chains. At the instance's typecheck — world ready — `expTFun`
  (fully ATF-generic, `TCMisc.hs:256-270`) expands each application into a ground wanted,
  solved once and memoized in the ATF cache; the numeric tower normalizes to a numeral. No
  generation-time solver, no ordering cliff, no staleness (nothing is snapshotted at
  generation), and `Bits` being declared `coherent` makes every such solve cache-admissible.
  This supersedes the earlier idea of a generation-time mini-TI for Deriving (that machinery
  remains relevant only to GenWrap's picks, where genuine *choices* are made; widths involve no
  choice, only deferred arithmetic).
- **Contexts:** monomorphic instances get **empty contexts** — the body's ground wanteds
  (`pack`/`==` on concrete fields) solve during the instance's own typecheck; no solver at
  generation, and the P3 discharge win falls out with no machinery. Polymorphic instances keep
  exactly the per-field `Bits`/`Eq` preds (the genuine API), deduplicated, and lose the
  arithmetic scaffolding (the fresh-var `Add`/`Max`/padding chains) to SizeOf expressions.
- **No enabling change needed:** type functions in fundep-*output* positions of instance heads
  are already legal — `checkNoTypeFunInHead` (`MakeSymTab.hs:448-475`) bans them only in
  non-determined positions, with the soundness argument stated in its own comment ("determined
  in EVERY functional dependency… never used as a source for instance matching"). So the
  derived heads this lane emits are accepted today, and the lane is a **Deriving-only change**.
- **One dependency to protect:** the operational mechanism that makes output-position type
  functions work is the instance-head expansion (`ctxRedInstHead`/`expTFun` turning each
  `SizeOf A` into a fresh var plus a `Bits A _` instance proviso — once, at declaration, in the
  defining scope, at ground heads: a valid-regime solve). P4/P5 must **relocate this expansion
  point, not delete it** — J4's destination is thereby refined: keep the expansion function,
  made unconditional where output-position TFs are present, moved to instance
  registration/typecheck; what dies is the use-only-if-nonempty conditionality and any
  rewriting of matching (input) positions — the parts the audit called architecturally unsound.
- **Why it is a P1 prerequisite, not a P4 nicety:** the audit's blowup benchmark (52× `.bo`,
  unfinished typecheck) measured reducible provisos preserved in signatures and re-solved at
  every importing use. Under P1, signatures stop being reduced — so constraint-laden derived
  instances (the highest-volume proviso source) would ship raw to every importer and recreate
  that shape. Born-reduced generation delivers generated code already in the form the retired
  pass used to produce.
- Scope companions: the CtxRed audit's "Deriving Generic must generate its hidden
  representation obligations explicitly" is this move for one class; GenWrap's pick-time
  boundary derivation (J2/J9) is this move for the wrapper machinery.
- Bonus: generation-time failures blame the right thing ("field f of MyUnion has no Bits
  instance") instead of surfacing as solver residue.
- **Landable now, and expected to speed up large-union typechecking on its own** (2026-08-22):
  today an N-constructor union's derived `Bits` emits ~3N fresh tyvars in three *interlinked*
  chains, so `reducePredsAggressive` runs a symbolic fixpoint (`joinNeededCtxs` re-sorts;
  `satMany'` restarts after each FD improvement). The SizeOf form replaces that with N
  *independent* ground solves (one `matchTop` each, ATF-cache-memoized across instances and
  packages) plus a linear `normTAp` fold — a complexity-class change in the constraint layer,
  with no dependence on P0–P5 (output-position TFs in heads are legal; `ctxRedInstHead`
  already expands them). First experiment: prototype `doDBits`/`doDEq`, benchmark on the
  largest in-house instruction package + a synthetic wide-union sweep + the audit's N×M.
  Parity rows must include **recursive types** (List/Rose-shaped), the common case exercising
  the recursive-dictionary knot — these rows land in the structural lane, not the width lane;
  see the jurisdiction bullet below.
- **Recursive types: the reducer's last legitimate jurisdiction** (2026-08-23, Ravi). The width
  lane never meets recursion — a recursive type has no finite width, hence no `Bits` instance to
  derive — but the structural classes (`Eq`/`Ord`/`FShow`/…) do, and there Deriving *free-rides
  on the pass being retired*: `doDEq` emits `Eq t` for every constructor-argument type verbatim
  (`Deriving.hs:275`), so `data List a` ships context `(Eq a, Eq (List a))` and mutually
  recursive families ship cross-reference chains; CtxRed is what reduces these to `(Eq a)`.
  Under P1 with nothing else done, every derived instance of a recursive type would carry its
  self-constraint into the `.bo` — an extra dictionary argument knot-tied at every importer's
  use site, and exactly the proviso-shipping shape the audit's blowup measured. Deferral (the
  SizeOf trick) does not apply: there is no closed form for `Eq (List a)`'s context — it must be
  *computed*, and the computation **is** context reduction. The resolution is jurisdictional,
  not architectural: derived instances have **no written context** — the generator defines it —
  so the no-rewriting rule is not engaged, and H98 §10 / GHC's `simplifyDeriv` establish
  fixpoint inference as the *specification* of derived contexts. Mechanism: keep the J1 core as
  a post-derive `inferDerivedContexts` pass over generated `Cinstance`s only. The environment it
  needs already exists at the right pipeline point: `symt11` is rebuilt immediately after
  Deriving "because Deriving added new instances" (`bsc.hs:401-403`), so imported instances
  *and* the group's own heads are both in scope. Rules: reduce constructor-headed preds only;
  a pred that is a group instance's head at its own instantiation is discharged as an assumption
  (the knot in generative form — mutual families converge the way `sat`'s `lookfor` stack does);
  group heads at other instantiations unfold under a depth cap (polymorphic recursion), and on
  cap the pred stays in the context — sound, merely noisy; open-class preds and tyvar-headed
  residue always stay. Multi-step recursion through library types falls out because imports are
  ready even at derive time: `Rose a = Rose a (List (Rose a))` → wanted `Eq (List (Rose a))` →
  via the imported `List` instance → `Eq (Rose a)` → group-self → discharge, residue `(Eq a)`.
  Parity criterion: inferred contexts must equal today's reduced ones across List/Rose/mutual-
  family shapes.

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
- **Scaling notes for large given/proviso pools** (imported GHC lessons): the store must be
  trie-indexed, never scanned — dictionaries keyed by class then argument types, equalities
  keyed by LHS tyvar, so lookups cost the size of the *type*, not the pool (BSC's `PredTrie`
  on fundep input positions is the same idea, today applied only to the instance table; the
  contrast receipt is `sat` recomputing `concatMap bySuperE ps` — the full superclass closure
  of the whole given pool — per wanted, `TCMisc.hs:370-381`). Superclass expansion is
  demand-driven, one layer at a time (eager closure is quadratic in deep hierarchies).
  Kick-out needs engineered criteria and, in the leveled store, is bounded per implication
  level. Honest caveat: GHC is untested at hundreds of givens per scope, a regime BSC's
  generated code reaches — but the numeric bulk of such pools lives in the simplex tableau
  (built for exactly that), born-reduced Deriving empties most generated pools before the
  store sees them, and the audit's N×M benchmark is already this phase's stress gate.
- **Cache admission = coherent ∧ ground.** The ATF cache already enforces the coherence half
  (the incoherent path in `sat` refuses to record, `TCMisc.hs:400-411`) but has no visible
  groundness guard on `recordATFs` (`:326-333, :396`) — and the guard is reachable: a
  sole-catch-all class with an empty instance context (the §1 `SplitPorts` scenario) fully
  discharges at a variable head, which would record `PortsOf t = Port t` — a for-all claim —
  as if canonical. Today the sacrificial `()` instance shields the cache by accident; under
  this plan an explicit groundness condition takes over that duty. Verify current behavior and
  add the guard as part of this phase.

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
- **Admission rule either way** (§1 validity criterion): discharge only constraints whose heads
  are coherent ∧ world-closed — today decidable only for the StdPrel computed classes (plus
  whatever the P0 regime census justifies for single-total-instance heads). If user-defined
  classes should ever be discharge-eligible, that requires a **closed-class marker** — the
  term-level sibling of GHC closed type families (which exist precisely because solve-no-search
  needs extension-proofness; PureScript instance chains are the related art). Open-world heads
  never discharge into the ABI; they freeze at boundaries or stay use-site-solved.

**Exit:** cross-package link-level differential tests (mixed old/new callers impossible by tag,
but mixed w/w and non-w/w defs within one build must interoperate); perf fence green; a
one-page record of which option was taken and the measurements that decided it.

### Phase 4 — Retire the targeted reducers, job by job

Kill list, each with its own parity test (see inventory for destinations):
J2/J9 → pick-time ground solves (with the contracts work; GenWrap stops floating constraints);
J4 → written instance heads for matching (input) positions; the output-position type-function
expansion is **kept and relocated** to instance registration/typecheck, made unconditional
(see §3.5) — what dies is the use-only-if-nonempty conditionality and any input-position
rewriting (gated on the Phase 0 head census — any head whose meaning shifts is a loud error
with migration guidance, not a silent change); J5/J6 → require-empty annotation checker;
J3 → ordinary typecheck of defaults; J7 → ATF-cache content parity without CtxRed's
contribution; J8 → `recordPackageUse` in typecheck + unused-import warning parity.

Also in this phase: **retire the sacrificial-instance idiom.** Once open classes are never
committed at non-ground heads, `Prelude.bs:4885-4887`'s XXX and the instance-count workaround
it documents become dead; declare openness explicitly instead — an `open`/overridable class
marker, the dual of P3's closed-class marker, so the deferral regime is stated rather than
encoded by how many instances happen to exist. Parity test: a class with ONLY a catch-all
instance, overridden from another package — the override must win at every use site (this
fails today; it is the acceptance test for the whole criterion).

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
- **R2 — The incoherence split is the coherence half of the validity criterion; the closedness
  half is unenforced**: CtxRed's `runTI flags False` ("XXX why?", `CtxRed.hs:40-41, 52-53`) is
  now understood — early reduction on an incoherent match is invalid, so the pass defers it —
  and the XXX should be answered in-code with the §1 criterion. The residual risk is twofold:
  (a) confirm no code path depends on the *difference* in when incoherent matching is attempted
  as work moves between passes; (b) world-closedness is assumed, never checked — the current
  pass will discharge a coherent-looking match that a downstream overlapping instance can
  re-open, a latent cross-package meaning change that the P0 regime census sizes and the P3
  admission rule eliminates going forward.
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

## 6. Open exploration (separable from the retirement plan): the numeric engine

A design position from the 2026-08-22 discussion, recorded for a future proposal; nothing in
P0–P5 depends on it.

- **Interface stays structural.** `TAdd` and friends are `TIabstract` type constructors
  (`Type.hs:116`), not ATFs — referring to `TAdd#(a,b)` costs nothing, and it must stay that
  way. Reifying numerics into per-reference constraints is GHC's mistake (the
  `ghc-typelits-natnormalise` / KnownNat experience: reference-tax noise from the encoding, an
  engine patch that cannot remove it). The compiler's existing prim-TF vs `TIatf` split
  (`isPrimTFunName`) is the right architecture. Principled version: primitive numerics have a
  closed decidable equational theory → structure in the type algebra; user ATFs' theory is the
  instance table → reified and ground-solved. Uniformity in either direction is wrong.
- **The ground tier stays fused into substitution.** `apSub` itself evaluates ground numeric
  applications (`Subst.hs:218` → `normTAp`/`opNumT`) — algebra applies immediately at type
  formation, and the satisfy↔apSub cascade (forced fact → substitution → downstream arithmetic
  collapses → more instances match) is how inference makes progress. Any engine change must
  keep feeding this cascade.
- **The replacement candidate is the symbolic tier inside satisfy** — and only that: `mgu` is
  deliberately theory-free (numeric and ATF disagreements become deferred equalities,
  `Unify.hs:56-77`), so every non-syntactic numeric fact already pools at one choke point. What
  would be replaced: the per-class inversion pattern tables (`genAddInsts` etc.), the
  cancellation laws encoded as NumEq implied instances (`StdPrel.hs:143-160`), and the
  `satMany'`/`joinNeededCtxs` fixpoint — for the numeric fragment only; user-class fundep
  matching stays in `matchTop`.
- **Spec: an incremental solved-form constraint store, not an end-of-inference certifier.**
  Assert numeric preds as they arrive; keep the store simplified in flight; emit *entailed*
  facts (forced values, forced equalities) as substitutions immediately so the cascade
  continues. Embodiments: Dutertre–de Moura incremental simplex with theory propagation
  (Yices2's core — vendored in-tree, though today used only by the scheduler); CLP(X)/HM(X)
  constraint stores; GHC's inert set — which converges with P2: the numeric engine becomes a
  theory component of the same store the evidence cache lives in. Batch QE (Omega/Cooper;
  pure-Haskell `presburger`) demotes to generalization-boundary completeness checks and
  unsat-core error reporting.
- **Guardrail (the validity criterion again):** propagate only entailed facts — never the
  solver's internal model. A model value is a guess: order- and version-dependent, incoherent.
  Solve, no search.
- **What it buys:** subtraction/partiality handled natively (where SOP-normalization engines
  die; `opNumT`'s `x >= y` guard marks the spot); first-class `≤` retiring the
  `Add#(pad,b,c)` dummy-variable idiom in user code and in `doDBits`' generated padding vars;
  order-independent improvement (the R3 bug class dead for numerics by construction);
  completeness for the linear fragment (fewer solver-hint provisos).
- **Sizing:** extend the P0 census to log which inversion patterns and `num_eqs` shapes fire in
  the wild; expected: the demanded fragment is overwhelmingly Presburger (mul/div by constants
  are linear), with symbolic `TLog`/`TExp`/`TMul n m` residue kept on today's special cases.
- **Prior-art verdicts:** Cryptol (production Z3-backed numeric typing for a decade;
  version-sensitivity and blame pains), GHC `type-nat-solver` (Diatchki 2015 — improvement via
  forced-value extraction works; never mainstreamed), `ghc-typelits-natnormalise` (evidence
  against reified interfaces, not against engines).
- **The store is also the prerequisite for higher-rank types and GADTs**, should those reach
  the language's horizon: OutsideIn(X) exists *because* GADT matches introduce branch-local
  Given equalities, which eager-unification inference cannot host (GHC's wobbly- and boxy-types
  attempts both failed before the constraint-store rewrite); arbitrary-rank checking needs the
  same implication scaffolding (skolemize, solve under the scope, untouchables). BSC is closer
  than it looks — `EPred`/`VPred` is the Given/Wanted split, `bySuperE` is given-superclass
  expansion, `tsBoundTyVarStack` is already a leveled skolem stack (`TIMonad.hs:322-327`),
  deferred equalities are canonical work items — what is missing is first-class implications,
  flavour-aware rewriting, and the store with kick-out. Design consequence for P2: give the
  store push/pop implication *levels* (per-level givens and untouchables) even though v1 uses
  one level; retrofitting levels is where GHC spent years. Payoff specific to hardware: GADT
  branch refinement here is *numeric* (`case instr of Add … ⊢ w ~ 32`), so the GADT givens and
  the numeric theory component compose in the same store — width-indexed encodings typecheck
  per branch. This changes P2's cost accounting from "cleanup enabler" to shared type-system
  infrastructure with three consumers.
- **Two-population store architecture (large-type scaling, e.g. big instruction unions):**
  facts that are ground ∧ coherent are scope-independent by the validity criterion and belong
  in the **global fact cache** (ATF/evidence — trie-indexed, monotone, shared, lookup-only at
  any size), never in a scoped store; only genuine *hypotheticals* (branch refinements,
  skolem-contingent equalities) are resident givens, and a match injects only the arm's own
  index instantiation (`w ~ 32`) into a pushed-and-popped level — a 200-constructor union costs
  200 tiny scopes, linear in the code written. The type's width closure never materializes as
  givens at all: it lives as ATF applications — *names for facts* — inert until a reference
  site expands them, whereupon they solve ground into the global cache. The store holds a
  **frontier, not a closure** (GHC's lazy-superclass lesson generalized; the SizeOf deferral
  of §3.5 is simultaneously this laziness mechanism). Worst case (a computation touching every
  constructor's width) forces the closure once, memoized globally — eager cost paid a single
  time, shared. Soundness note: lazy materialization varies expansion order with reference
  order, which is harmless exactly because every solve is coherent ∧ ground (solve, no
  search) — the criterion is what makes the laziness safe, not just the caches admissible.
- **The headline language payoff — numeric refinement case — needs less than full GADTs.**
  A case over a type-level number via compiler-provided *views* (`Zero`/`Succ m`, comparison
  views yielding `≤` givens) keeps the definition `forall n` while each arm typechecks under a
  branch-local numeric given (`n ~ 0`, `n ~ m+1`) that the numeric theory component propagates
  into the arm's width arithmetic — `Bit n` splits as `Bit 1 ++ Bit m` with no coercion, the
  recursive call at `m` typechecks. Requirements are exactly the stack above: store levels,
  numeric theory component, a small view construct, and an exhaustiveness-checker extension
  (T0165/T0166) for view completeness — no user-visible GADT constructors. BSC does this
  *better* than the GHC/Clash encoding it resembles: no KnownNat plague (the compiler owns
  numerals; `valueOf` already bridges), and no runtime-representation question (elaboration is
  total static evaluation and synthesis grounds `n`, so the case is a staged conditional —
  today's `if (valueOf(n) == 0)` generator idiom made type-sound). It retires the
  typeclass-instance recursion encoding for width-recursive generators (adder trees, shifters,
  encoders) — the catch-all/overlap world — in favor of one polymorphic definition with
  branch-local knowledge. Termination and never-grounding are today's stories (steps budget;
  synthesis monomorphization).

## 7. What stays forever

Constraint solving itself (`sat`/`reducePred` in the typechecker), the ATF solve-no-search
machinery, coherence enforcement (T0158), and the raw written telescope as the single source of
identity. What dies is one thing only: the package-wide pass's authority to rewrite declared
types — and then the pass itself.
