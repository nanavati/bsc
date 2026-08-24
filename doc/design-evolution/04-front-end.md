# 04 — The Front End: Coherence, Closure, and the Typechecker

The type-system evolution: the coherence stack, the closure doctrine,
CtxRed retirement, visible type application, ATF evaluation, deriving,
the numeric engine, pattern checking, and the metadata substrates.

**Status:** v1.0 — 2026-08-24 (Claude, holistic review). Labels: FACT /
DECISION / PROPOSAL / RESOLUTION / NEEDS-RAVI.

## 1. The closure doctrine (the unifying theorem — RESOLUTION: state it once)

Three lanes independently derived the same licensing rule; this
document names it once so the three stay one:

> Early commitment to an instance/equation is meaning-preserving
> exactly when the match is **coherent** and **closed** — type-closed
> (no pending instantiation can redirect it) and world-closed (no
> future instance can redirect it).

Its three enforcements:

- **Typeclass level** (the coherence stack): ordered-clause fundep
  semantics; commitment when no earlier instance may capture and no
  given may discharge; modal-vs-actual judgment with the unguarded
  unifier; bound-variable discipline (rigid variables never acquire
  bindings); coherence is *type soundness* in bsc, because ATFs reduce
  through instance selection with no coercion layer.
- **ATF level**: "the judgment boundary is the persistence boundary" —
  persisting phases only evaluate, over sealed equation sets;
  ATF-carrying families are sealed-overlapping or nonoverlapping-open
  by declaration; strong incoherence and ATFs are mutually exclusive;
  the rule table is a monotone log of sealed families.
- **CtxRed level** (the validity criterion, Ravi): commitment tiering —
  declared-open classes defer until ground; ordinary classes commit on
  a clean unify-guard (an instance head stakes an exclusive claim to
  its unification cone); long-term, no-overlap as the language default.
  The **orphan ban makes world-closure checkable** (promote WOrphanInst
  to error; GenSign already computes the fundep-aware check).

RESOLUTION (adopting Codex across the three lanes): closure must be
*enforced and carried as evidence*, not assumed — a machine-checked
stable-family certificate; class-policy and equation-set digests in
interface/action keys; selected-derivation identity recorded; ground
reduction results memoized only within a frozen rule snapshot (the
session context of 01 §3); one shared pure ground kernel for
typechecker instance resolution and ATF evaluation (no drifting second
solver), returning typed results (Reduced / Dormant / typed failure)
with the expandSynN escape removed once asserted unreachable.

## 2. The coherence stack and the orphan program (status + resolutions)

FACT: upstream stack #1032 (merged) → #1033 keywords → #1035 ordered-
clause commitment → #1036 batched numeric settlement (FloatingPoint
501→24 solver sessions, −26% wall) → #1037 bound-variable discipline →
#1038 solved-dictionary pool; idle since 07-15 awaiting review.
The orphan-mislink work adds five demonstrated silent hardware
mislinks, the GenSign synonym-omission defect, and the use-site
rejection design with the interchange/computational class taxonomy and
a declared opt-in for behavioral orphans.

A companion principle the dev note names and other lanes should adopt:
**modal vs committed judgment** — "guarded modal checks turn 'not yet'
into 'never', and in a commitment regime 'never' is what licenses a
commit." Anywhere the toolchain commits early (scheduling, ATF
sealing, pool reuse), viability checks run unguarded.

Hard sequencing facts (FACT, from the dev note): lift-dictionaries'
type-keyed cross-package dedup is UNSOUND until the walk-integrity
fixes (H6 trie leaf ordering, B1 stuck-ATF keying) land;
transitive-incoherent lands first with zero conflict surface; CtxRed
retirement requires the explicit givens guard (now implemented) and
remains an ABI-exposed restructure; cross-package overlap detection is
unpinned (A8) — the concrete open surface behind the DAG's N2.

RESOLUTIONS: fix GenSign first (expanded-head keep/drop + orphan
classification; silent signature omission becomes an error for
annotated classes). Use-site rejection is the enforcement point
(owner-declared no-orphans property + representation-owning parameter
projection; normalize synonyms/ATFs before classification; refuse
conservatively when a head cannot be normalized). Instance-environment/
evidence digests join manifests (T2) — coherence evidence is global
artifact and ABI identity; ABI-selecting classes (Bits, SplitPorts,
Wrap*, ValidateBits, Literal/RealLiteral, Huffman codebooks) are
physical-boundary inputs. The dev-note mirror gets a semantic-
supersession banner (input-driven ordered-clause semantics landed;
suffix-scan prose is historical). #1033's keyword syntax reserves room
for the no-orphans property so the two changes compose.

## 3. CtxRed retirement and visible type application

The plan of record (v0.1 + the 16:54 extensions): jobs J1–J11, phases
P0–P5, organized by *the written form is identity; solved facts are a
cache*. Signatures serialize raw written telescopes (P1) — the landing
precondition for **VTA** (implemented; blocked precisely because CtxRed
can erase/merge/move written binder slots). The internal canonicalizer
+ evidence cache (P2) is the same mechanism as the definition cache and
the ATF cache. Born-reduced deriving (emit closed TAdd/TLog forms;
N independent ground solves) is landable now and is the immediate
empirical test of the constraint-layer thesis. J11 (derived-context
inference as the *specification* of derived contexts) stands with
Codex's condition adopted: reduce only against a sealed coherence/rule
snapshot whose identity enters the artifact — it is a semantic artifact
producer, so it lands after the format registry and coherence
enforcement. Value-CAF recursion blocks at derive time (provable cycles
only). Numeric-engine exploration keeps bsc's structural interface and
swaps the engine behind satisfy: three incomparable axes — ring-
equational (MulTerms/SOP; natnormalise as reference spec), Presburger
(complete for linear/order/div-by-constant), monotone-bounds lattice —
combined by purification; the **policy ceiling** "complete where
decidable, axiomatic where not, heuristic never" is NEEDS-RAVI, with
Codex's amendment folded in: the operative rule is *no uncheckable or
non-monotone acceptance* (certified deterministic tactics are
admissible; portfolio disagreement handling required; solver identity
and resource policy in cache keys; never cache resource-dependent
UNKNOWN).

RESOLUTION (solver ownership): the scheduler's solver and the
typechecker's entailment backstop get separate configuration, rollout,
cache identity, and typed failure taxonomies even while sharing
engines; any scheduler-solver change is a flag-day (UNKNOWN-
conservative verdicts move borderline facts into bytes); the
typechecker's residual entailment seam may use a pinned external worker
(classify interactions, not components) while improvement/unification
stays native — the conversational-algebra exclusion stands.

## 4. The metadata substrates (IType, IExpr, notes)

FACT: measured and implemented on the fork — IType WHNF-only rnf,
interned ftv sets with substitution pruning, the ATF-free bit
(architectural, audited); IExpr fv caches (superset rule; knot rule
with the ICValue acyclicity correction), content hashing with
rank-first comparison (fixing a real Ord transitivity cycle — upstream
candidate), the falsified predicate-interning probe, the profiling
exemption law, and the calibrated machine-independent perf boundary
(bsc.evaluator/itype-sharing). The phase-indexed notes design is the
structural successor: only a type index is a sound phase signal
(construction thunks cross phases through the IConv/FixupDefs knots);
FV/HashNote/() instances delete both cross-phase taxes.

RESOLUTIONS: the session-context program of 01 §3 owns all lifetimes
here; heap identity stays out of durable hashes ("comparison
fingerprint"); dense-substitution is stated as the weaker bound with a
benchmark. FALSIFIED (Ravi, 2026-08-24): the typechecker substitution
remedy sketched as a persistent union-find binding forest did not pan
out — most type variables are dropped quickly and do not form alias
chains that union-find would help. The statement-count quadratic
remains real and unremedied; the standing rule (one cost-centre
profile of the reproducer before any surgery) now gates whatever
replacement approach is proposed next.

## 5. Language-surface work (settled shapes)

- **Pattern checking** (stack #14→#15→#13): Maranget usefulness;
  on-by-default after the guard-fold fix; negative literals with
  type-directed NegRule semantics; Real = BSV parser parity. Adopted
  review conditions: reconcile the negative-UInt prose into four
  explicit cases; masks are value-set membership, never ICUndet/X
  (cross-policy tests); cache column kinds only post-normalization;
  export per-obligation completeness (fuel abandonment must be visible
  to LSP/verdicts). STATUS CORRECTION (meeting record, 10 §5):
  exhaustiveness checking is DEFERRED pending further testing and a
  rebase onto recent upstream — the implementation fails on specific
  hardware values and needs a standalone test approach, and
  synthesizability of checked constructs is a hard requirement. The
  design above stands; the deployment claim does not, yet.
- **Language-extension policy** (DECISION, 2026-08-15): consult the
  literature before designing; VTA followed it (specified/generalized
  binders, deterministic source order, no explicit-forall
  prerequisite).
- **Deriving via + '0/'1 classic literals**: implemented in the trs
  compat port, upstream-PR-shaped; landing route NEEDS-RAVI. The
  unsized-bit-literal wishlist item of the March internal sync is the
  recorded origin (10 §5).
- ValidateBits carries a recorded internal feature ask and is already
  deployed as a production validation pattern (07 §5) — see 05.
- **Small-project inventory** (ramp menu, 10 §6): first-class ===
  (generic emulation cannot reach tagged-union tag tests; Eq-method vs
  built-in is the open design question); the TypeError typeclass
  (upstream #286); both are typechecker-surface work that composes with
  this document's error-reporting and coherence programs.

## 6. Meeting-sourced history: dictionaries, wrappers, and strictness

The meeting crawl (10 §5) recovered the documented pre-history of this
document's §§2–4 programs; recorded here because it grounds them:

- **The WrapField regression** (performance-assessment engagement,
  Sep 2025): the fork's typeclass-driven wrapping (WrapField/WrapMethod/
  SplitPorts) gives WrapField a String field-name type argument so
  context-reduction failures can name the failing field. That argument
  defeats joinNeededCtxs context joining, so blasting a Vector of
  interfaces constructs the *same* dictionaries once per element — the
  root-caused compile-time regression (commit 372bee64). Three fixes on
  record (Ravi): drop the element index from the field name so contexts
  join; join specially after reduction to WrapMethod (no String arg);
  or CSE the generated dictionary code (partial precedent:
  simplifyDictBindings), carefully not CSEing non-dictionary code whose
  names feed errors and readable Verilog. Any chosen fix must
  co-compose with §2's evidence-digest and dictionary-pool work.
- **The wrapper dictionary flow-through defect** (compiler tour): the
  wrapper phase *reconstructs* the big dictionaries the first typecheck
  already built — "you should just look it up; we do not flow that
  properly." The same enumeration-principle shape as T1: a
  recompute-and-discard boundary fact waiting to be carried forward.
- **The deriving-after-genwrap ordering defect** (tour): wrapper
  generation cannot see the full instance universe because deriving
  runs after it — a known structural wart on §2's coherence story and
  the ramp trajectory's named destination.
- **Strictness and Hyper→NFData**: Hyper predates NFData and its
  replacement (upstream #811) is worth ~13% alone; the surgical
  proposal of record makes ISyntax strict in everything except ICon's
  IConInfo (eSubst never substitutes into ICon; laziness must survive
  for the ICDef/ICValue/IClock/IReset/IInout/ILazyArray knots) — the
  same knot-topology facts that §4's substrates and the notes design
  build on.
- **Sequencing confirmation**: strictness annotations plus ground-type
  interning are being sequenced specifically to enable dictionary
  lifting, whose fix is flagged as the urgent, prioritized soundness
  item for the recent release — independently matching §2's hard
  sequencing facts. A union-find
  typechecker architecture was proposed in the same meeting arc (with
  "purity essential for tooling compatibility" and a systematic
  invariant-checking policy to be agreed upstream) but was subsequently
  FALSIFIED — see §4; the purity and invariant-checking commitments
  survive the falsified mechanism.
- **Numeric-engine motivation** (tour): today's two-level system
  (handcrafted simplifying instances, then thumbs-up/down SMT) cannot
  learn (knows a+a=2a, not a+2a=3a) — the operative wish behind §3's
  three-axis exploration. A fundep-improvement fix is expected to open
  higher-rank types via GADT-style reasoning (Mar 27) — the front end's
  stated growth direction (00 §3).

## 7. Lane pointers

"KB: bsc typeclass coherence" (+ dev-note mirror); "KB: bsc ATF rewrite
rules design"; "KB: bsc toolchain" HEAD (VTA, CtxRed audit + plan) and
continuation (16:54 extensions; PVM determinism); "KB: bsc solver
strategy"; "KB: bsc IType interning perf boundaries"; "KB: bsc IExpr
metadata and notes design"; "KB: bsc pattern-match checking";
CTXRED-RETIREMENT-PLAN.md; upstream #950, #964, #1042, #1061.

## 8. NEEDS-RAVI (rolled up in 09)

- Ratify the policy ceiling (as amended) and the solver-ownership
  split.
- Coherence stack: push for upstream review (idle since 07-15); the
  post-port full-suite seal.
- WOrphanInst→error timing; GenSign filing route; whether the
  orphan-mislink findings comment on #1061 or file separately.
- CtxRed P1 sequencing vs the VTA branch; born-reduced deriving
  experiment authorization.
- IExpr/IType landing calls: the fork-CI 4-cell matrix verdict, the
  one-golden regold, rank-first Ord upstream forwarding.
- The WrapField fix choice (§6): field-name normalization vs
  join-after-WrapMethod vs dictionary CSE — pick the lane so the
  evidence-digest work builds against it.
- Pattern-check: the fuel-observability diagnostic and the full-suite
  seal per 01's capability rules.
