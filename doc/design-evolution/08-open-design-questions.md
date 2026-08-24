# 08 — Open Design Questions

The destination choices that need Ravi's ruling before the design
(00–07) is agreed. Design questions only: no venues, schedules,
funding, staffing, or custody — those live in the KB lanes and are
deliberately out of scope until the destination is settled. Every OPEN
item in 01–07 appears here; nothing here lacks a home there.

**Status:** v2.1 — 2026-08-24 (Claude).

## A. Cross-cutting ratifications

1. **The identity root (01 §2).** Ratify the format registry +
   transitive manifest as the design's root artifact — one tag
   registry, five-identity manifests, fail-closed readers — and the
   contract-files ↔ manifest unification (one artifact family, not
   two).
2. **The observable-event contract (03 §2, 05 §3).** Define once, for
   every engine: when $finish takes effect, coincident-edge guard
   snapshot semantics, and the guard-evaluation/execution split under
   dynamic alternatives. The finish clause is defined; the rest is
   open, and stored oracles cannot be re-pinned until it is.
   Language-level.
3. **The solver policy ceiling (04 §4).** Ratify "complete where
   decidable, axiomatic where not — no uncheckable or non-monotone
   acceptance" as the permanent acceptance-frontier rule; the
   scheduler-vs-typechecker ownership split with the flag-day rule;
   the packaging corollary (heavy proof stacks ship with the
   simulation platform, never core bsc); and the manifest's
   solver-identity and resource-policy field set (01 §8).
4. **The divergence policy (T9).** Adopt the operational form as
   decision-of-record: any fork divergence is pinned, declared in
   artifact identity, and carries an upstream exit plan.
5. **The session architecture (01 §3).** Ratify the three-lifetime
   model (node-local / arena-generation / semantic-snapshot) as the
   binding rule for every memo, cache, and long-lived worker.

## B. Per-area design choices

6. **Codebook adoption (02 §3):** freeze the existing planner's
   behavior as the ABI (exact port, differential-fuzz-witnessed) vs
   canonicalize a documented planner on both sides — a choice
   foreclosed once any frozen deployment of the encoding exists.
7. **BVI fallback and foreign execution (02 §4):** ratify the
   structural binding design — explicit binding map, call-context
   refinement check, sealed stub witnesses, harness-side warnings —
   as the v1 semantic scope; and whether strict conformance mode is
   the default for foreign execution.
8. **ValidateBits residuals (05 §2.5):** the completeness bound; the
   non-blessed-configuration diagnostic (warn vs error); the reserved
   unknown-arm spelling; the blessed X-lane defaults. Plus the two
   deeper questions: **value-X vs condition-X** (05 §2.1 — both
   positions on record; the write-up with soundness argument is the
   agreed vehicle), and whether an ecosystem-visible primitive may
   have its reference semantics defined by the internal 3-state
   simulator or must pin a simulator-independent spec.
9. **Coverage design (05 §6):** the register-mux rendered form; SVA
   cover vs covergroup emission; guard-conjunct capture placement;
   whether rule-body line coverage is ever worth its cost.
10. **The kernel-ABI extension (06 §1, 05 §5):** does the simulation
    kernel gain a write path (poke/deposit) and a synchronous
    stepping API? One coordinated design decision over all consumers
    (scripting, fuzzing, lockstep drivers) — the sidecar-stimulus
    route covers most needs without either.
11. **Orphan enforcement residuals (04 §2, §8):** the final
    no-orphans property shape; audit-mode vs warn-at-use for declared
    behavioral orphans; whether (and under what conditions) the
    signature-omission class is an error.
12. **The wrapper-class dictionary economy (04 §3):** drop the
    per-element index from the field-name argument vs join after
    reduction to the name-free class vs generated-dictionary CSE —
    the evidence-digest design builds against the chosen mechanism.
13. **Parser implementation (06 §2):** the combinator route vs the
    LALR(1) port, under the settled modernization decision (ranges,
    recovery, comments-survive-lexing are invariant either way).
14. **The interop-ABI clause queue (02 §8):** canonical form (clause
    1); anonymous/structural types at boundaries; recursive encoded
    types.
15. **$random (05 §3):** one-generator-everywhere and/or the
    source-level per-instance randomizer as the language's answer.
16. **SplitPorts live alternatives (02 §2):** the split-structure
    design's rejected alternatives that remain open until measurement
    — pick the design on evidence, not by default.
17. **Docstring standard (06 §2):** the marker and attachment rule
    (comments-survive-lexing is step zero regardless).
18. **The clean-suite definition (01 §5, §8):** zero unexpected
    verdicts with capability-visible coverage as the acceptance bar —
    an unavailable capability reads as not-covered, never as a green
    skip.
19. **Touch-point provenance rendering (06 §2, §6):** how typeclass
    position universes and merged origins render for a single touch
    point, given that source-to-RTL provenance is a many-to-many DAG.

## C. Destination strategy (shapes the design itself)

20. **trs's ultimate home (07 §5.1):** side-tree product forever, or
    an eventual upstream offering — and in what form (tool suite vs
    backend). This decides whether BIR versioning is an internal or
    public contract, and whether "Bluesim remains" has an expiry for
    external users.
21. **The one-order break's ecosystem posture (03 §1, 07 §5.2):** the
    model is decided; what the design owes the installed base — the
    priced census, format generations, and a legacy reading mode are
    designed in — but whether the model is ever part of the shared
    language (vs living fork-side indefinitely) changes what "one
    language" means.
22. **Commercial-simulator depth (07 §5.3):** how much of the
    destination includes VCS-specific design (trs shell under VCS,
    encrypted-IP flows) versus treating VCS as test-time oracle only.
    Includes confirming 02 §5's transport reading (shell exports
    monomorphic ⇒ mangled DPI suffices; else VPI covers).
23. **The testsuite's destination (01 §5):** its design assumes the
    graph engine; if the engine's home is fork-only, the testsuite
    destination changes (the corpus stays on its current
    orchestration) — the premise is part of the destination, not just
    the plan.
24. **The scheduling model's accepted risks (03 §5):** the stated
    research risks — coordinate assignment IS the scheduling problem;
    the antichain bet — with the staged value proposition that if they
    fail, the arc stops at footprints + schedule values + verify mode.
    Accept that proposition as the model's risk posture.
