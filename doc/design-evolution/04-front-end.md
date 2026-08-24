# 04 — The Front End: Coherence, Closure, and the Typechecker

The type system's destination: the closure doctrine, coherence and
orphan enforcement, ATF evaluation, identity-not-cache for solved
facts, visible type application, deriving, the numeric engine, the
metadata substrates, and pattern checking.

**Status:** v2.0 — 2026-08-24 (Claude). Design only; sequencing,
status, and provenance live in the KB lanes, outside this set.

## 1. The closure doctrine

Three lanes independently derived the same licensing rule; stated
once:

> Early commitment to an instance/equation is meaning-preserving
> exactly when the match is **coherent** and **closed** — type-closed
> (no pending instantiation can redirect it) and world-closed (no
> future instance can redirect it).

Its three enforcements:

- **Typeclass level**: ordered-clause fundep semantics; commitment
  when no earlier instance may capture and no given may discharge;
  modal-vs-actual judgment with the unguarded unifier; bound-variable
  discipline (rigid variables never acquire bindings). Coherence is
  *type soundness* here, because ATFs reduce through instance
  selection with no coercion layer.
- **ATF level**: "the judgment boundary is the persistence boundary" —
  persisting phases only evaluate, over sealed equation sets;
  ATF-carrying families are sealed-overlapping or nonoverlapping-open
  by declaration; strong incoherence and ATFs are mutually exclusive;
  the rule table is a monotone log of sealed families.
- **Validity-criterion level**: commitment tiering — declared-open
  classes defer until ground; ordinary classes commit on a clean
  unify-guard (an instance head stakes an exclusive claim to its
  unification cone); long-term, no-overlap as the language default.
  The **orphan ban makes world-closure checkable**.

RESOLUTION: closure is *enforced and carried as evidence*, never
assumed — machine-checked stable-family certificates; class-policy and
equation-set digests in interface/action keys; selected-derivation
identity recorded; ground reductions memoized only within a frozen
rule snapshot (the session architecture, 01 §3); one shared pure
ground kernel for typechecker instance resolution and ATF evaluation
(no drifting second solver), returning typed results.

## 2. Coherence and the orphan program

The design: instance signatures are total and truthful (signature
keep/drop and orphan classification run on the same normalized heads —
a signature layer that silently omits instances makes every downstream
judgment a lie); orphan instances of representation-owning classes are
rejected at **use sites**, under an owner-declared no-orphans class
property with representation-owning parameter projection; heads are
normalized (synonyms/ATFs expanded) before classification, refusing
conservatively when a head cannot be normalized; declared behavioral
orphans are an explicit opt-in. *Why use-site and why error:* the
mislink study demonstrated silent hardware corruption from orphan
divergence, and definition-site warnings structurally cannot protect
the parties harmed — the importers. Instance-environment and evidence
digests join manifests: coherence evidence is global artifact and ABI
identity, because the ABI-selecting classes (Bits, SplitPorts, the
wrapper classes, ValidateBits, literal classes, codebooks) are
physical-boundary inputs.

Cross-package deduplication of solved dictionaries is sound only
under walk-integrity (deterministic leaf ordering; stuck-ATF keying)
and coherence enforcement — evidence identity precedes evidence
sharing.

## 3. Identity, not cache: retiring eager context reduction

The organizing principle (shared with 01 §4): **the written form is
identity; solved facts are a cache.** Signatures serialize raw written
telescopes; an internal canonicalizer plus an evidence cache replace
eager pre-persistence context reduction; derived contexts are
*specified* by inference against a sealed coherence/rule snapshot
whose identity enters the artifact. What this unblocks, by design:

- **Visible type application** — sound only when written binder
  telescopes are never erased, merged, or moved by a solver pass.
- **Born-reduced deriving** — derived instances emit closed
  arithmetic forms with N independent ground solves, rather than
  N-times-rediscovered constraint towers.
- **Value-level recursion blocking at derive time** (provable cycles
  only).

The historical rationale dissolves with the mechanism: eager
reduction existed to spare the typechecker re-solving derived-Bits
constraint towers; caches do that job without making solver output
part of artifact identity.

Two structural defects the evidence-flow design removes: wrapper
generation *reconstructs* the dictionaries the first typecheck already
built ("you should just look it up — we do not flow that properly"),
and deriving runs after wrapper generation, so wrappers cannot see the
full instance universe. Both are consequences of solved-fact flow
being ad hoc; both disappear when evidence is a first-class, carried
value.

A known dictionary-economy defect with three candidate designs: a
wrapper class carries a field-name type argument so context-reduction
failures can name the failing field, and that argument defeats
context joining — identical dictionaries are constructed once per
blasted vector element. The alternatives on record: drop the
per-element index from the field-name argument so contexts join; join
after reduction to the name-free class; or CSE generated dictionary
code (careful never to
CSE non-dictionary code, whose names feed errors and readable
Verilog). OPEN which lands (08); the evidence-digest design must
compose with whichever does.

## 4. The numeric engine

bsc keeps its structural interface and swaps the engine behind
satisfy: three incomparable axes — ring-equational (with an external
normalizer as reference spec), Presburger (complete for
linear/order/divisibility-by-constant), and a monotone-bounds lattice
— combined by purification. *Why:* the current two-level design
(handcrafted simplifying instances, then a thumbs-up/down SMT
fallback) cannot *learn* — it knows a+a=2a but cannot conclude
a+2a=3a; the axes name what completeness is available where. The
acceptance-frontier ceiling: **complete where decidable, axiomatic
where not — no uncheckable or non-monotone acceptance** (certified
deterministic tactics admissible; portfolio disagreement handling
required; solver identity and resource policy in cache keys; never
cache resource-dependent UNKNOWN). Numeric kinds remain naturals by
design ("no negatives" is load-bearing for the reasoning).

Solver ownership is split by consumer shape: batch-verdict consumers
(scheduling disjointness, X analysis) use pinned, bundled external
engines behind text seams; the typechecker's conversational algebra —
where answers feed back into question generation — stays native, with
at most a pinned external worker on the residual entailment seam
(classify interactions, not components). The packaging corollary:
heavy proof stacks ship with the simulation platform that consumes
them, never with core bsc — deferring any core-bundling question
until a core consumer exists. Any scheduler-solver change
is a flag-day under byte-exactness; the two consumers get separate
configuration, cache identity, and typed failure taxonomies even
while sharing engines. A rejected mechanism, kept as rationale: a
persistent union-find binding forest for typechecker substitution was
falsified — most type variables are dropped quickly and never form
alias chains; the statement-count quadratic is real but wants a
different remedy, and any remedy is gated on a cost-centre profile of
the reproducer first.

## 5. The metadata substrates

The IR carries its bookkeeping structurally: hash-consed types with
cached free-variable sets, substitution pruning, and an architectural
ATF-free bit; expression-level free-variable caches (superset rule;
knot rule with the acyclicity correction) and content hashing with
rank-first comparison (fixing a real ordering-law violation);
phase-indexed notes as the successor to boolean chicken flags — only a
type index is a sound phase signal, because construction thunks cross
phases through the conversion knots. Laziness carve-outs are explicit
and named: strict everywhere except the constructor arms that carry
cross-definition references and cycles (definitions, clocks, resets,
inouts, lazy arrays) — substitution never enters those arms, which is
what makes the strictness sound. Heap identity stays out of durable
hashes (comparison fingerprints, 01 §3); the session architecture
owns every lifetime.

## 6. Language-surface designs

- **Pattern checking**: Maranget usefulness; guard folding; negative
  literals with type-directed semantics; masks are value-set
  membership, never undefined-value tests (cross-policy tests);
  column kinds cached only post-normalization; per-obligation
  completeness exported so fuel abandonment is visible to editors and
  cached verdicts. Checked constructs must be synthesizable.
- **Extension policy** (DECISION): consult the literature before
  designing; visible type application followed it (specified/
  generalized binders, deterministic source order, no explicit-forall
  prerequisite).
- **Compat literals and deriving-via**: unsized '0/'1 classic
  literals and deriving-via are part of the language surface (origin:
  the ecosystem wishlist).
- **Library coherence law**: container instances obey the
  foldMap/traverse coherence law; an instance that cannot (a
  validity-gated container whose Foldable and Traversable would
  disagree) is removed rather than gated — forcing the payload
  decision to the user.
- **First-class structural equality** (===) and a TypeError typeclass
  for targeted missing-instance diagnostics are small settled-shape
  extensions on the inventory.
- Growth direction beyond the retirement: implication constraints and
  an inert-set store open numeric-refinement case statements,
  higher-rank types, and GADT-style reasoning (a fundep-improvement
  fix is the expected unlock).

## 7. Pointers

Mechanism and evidence: the coherence dev note and digest; the ATF
rules design; the CtxRed retirement plan; the solver-strategy record;
the IType/IExpr substrate records; the pattern-match design; the
orphan-mislink study. Indexed in the KB; open design decisions in 08.

## 8. RESOLUTIONS and OPEN questions

- RESOLUTION: closure carried as evidence; one shared ground kernel;
  evidence digests in manifests.
- RESOLUTION: use-site orphan rejection under owner-declared
  properties; signature totality fixed first.
- RESOLUTION: written-form identity with evidence caches; VTA and
  born-reduced deriving ride it.
- OPEN: the solver policy ceiling's ratification (as amended); the
  ownership split's flag-day rule.
- OPEN: the wrapper-class dictionary-economy fix (three candidates;
  08).
- OPEN: the orphan-enforcement residuals — the final no-orphans
  property shape; audit-mode vs warn-at-use for declared orphans;
  under what conditions signature omission is an error (08).
