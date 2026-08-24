# 09 — Open Questions for Ravi

Everything this review found that genuinely needs your call,
consolidated and prioritized. Per-lane detail lives in the cited
documents/lanes; this is the decision queue.

**Status:** v1.0 — 2026-08-24 (Claude, holistic review).

## A. Highest leverage (unblock multiple lanes)

1. **Ratify the DAG root (08):** the format registry + transitive
   manifest workstream as the first-funded node, including the
   recertification set for landed schema drift (PRs 47, 66, 67, 87,
   144, 151, 152; trs AOT rev-26 callback ABI). Nine lanes' review
   findings converge here.
2. **The observable event contract (03 §R3.2, 05):** define once, for
   every engine, when $finish takes effect, coincident-edge guard
   snapshot semantics, and the guard-evaluation/execution split for
   dynamic alternatives. Language-level; goldens re-record after it.
3. **Upstream review bandwidth (07 §4.4):** the coherence stack idle
   since July; trs PRs #108–#158 at zero review comments; the
   Bluespec, Inc. review program and the staffing memo are the levers
   (Monday's meeting), with the MSA + SoW draft as the ready
   instrument (07 §5) and the Unison sheet's terms proposed-not-agreed
   (06 §2).
4. **The solver policy ceiling (04 §3):** ratify "complete where
   decidable, axiomatic where not, heuristic never," as amended to
   "no uncheckable or non-monotone acceptance," as the permanent
   acceptance-frontier rule — plus the scheduler-vs-typechecker solver
   ownership split and flag-day rule. Packaging corollary the cross-cut
   surfaces as implied-but-never-stated: ship the X-analysis solver
   stack with trs (already MatX-packaged under the side-tree doctrine)
   rather than bundling ~30MB of engines into core bsc releases,
   deferring the upstream-bundling question until an upstream consumer
   exists — ratify or amend.
5. **One-order compatibility rung (03 §R3.1):** approve running the
   urgency/execution divergence census (today's scheduler; testsuite +
   a large internal corpus, 07) and the named-rung/format-generation
   treatment of the break — including the **venue** question the
   cross-cut raises: does one-order ship fork-first or upstream-first,
   and does the census also run over upstream corpora?
5a. **Two-tier landing rule (08 §2):** ratify (or amend) the policy
   that schema-serializing / cross-engine-identity work gates on N1
   while semantics-preserving work lands on its own evidence.

## B. Design ratifications waiting (single-lane, ready)

6. **HuffmanBits adoption gate:** (a) exact assign_tags port +
   differential fuzz vs the reference Rust tag tables (07 §2;
   recommended; Codex ACK) vs (b) canonicalize both sides (flag-day).
   Also: share the study's companion artifacts.
7. **BVI fallback (02 §4):** ratify the structural binding design with
   the review conditions as v1 scope; decide the soft-IP
   implementation's rebase route.
8. **ValidateBits residuals:** Q1 (completeness bound), Q3 (non-blessed
   config: warn vs error; lean warn-once-per-module), Q4 (reserve the
   unknown-arm spelling), Q6 (X-lane defaults; name the blessed
   two-knob configuration); the X-payload doctrine question (leans
   "payload X flows"); final D7-prose alignment. Plus the governance
   edge the cross-cut names: may an upstream-visible primitive have its
   reference semantics defined by the (internal) 3-state trs, or should
   the completeness bound be pinned in a simulator-independent spec?
   The X-payload question now has both positions on the transcript
   record (value-X vs condition-X; the write-up-with-soundness-proof
   action is the agreed resolution vehicle — 05 §4, 10 §5).
8a. **Coverage program (05 §6):** the proposal's own open questions —
   register-mux rendered form; SVA cover vs covergroup emission;
   guard-conjunct pass placement (cheap now, annoying to retrofit);
   rule-body-depth interest ranking; pilot-block selection — plus
   authorizing the audit probe and the pilot.
8b. **Two-state arc asks (05 §4):** the vendored-code lint-waiver home
   (blocks two test families); environment-conditional XFAIL policy
   for container-artifact failures; VCS validation + the
   SystemC-enabled acceptance run before upstreaming; optionally name
   the two-state conformance macro.
8c. **#158 merge gate:** approve the fresh full-corpus diffsweep seal
   as the gate before the REV-27 flag day merges (recommended
   in-lane; 05 §2).
9. **BVI-via-Verilator:** Q4 strict mode (recommendation on record:
   ratify strict); pick and provision the pinned Verilator (the fork
   release from the fixed tip); observability tier 2; landing the
   branch into the stack.
10. **bluehs sim scripting:** ratify the v1 bar (parity, no poke) and
    the first consumer (isolated-worker lockstep driver); the
    poke/deposit kernel-extension question — TIME-SENSITIVE per the
    cross-cut: poke is a bk_* kernel ABI change and the kernel ships
    with the freeze (07 §1), so this is the one "freeze-indifferent"
    claim that fails; decide in-or-out before the kernel freezes. The
    coordination surface widened (05 §5): the bk_sync stepping API
    exists on a branch and its author will produce a fuzzing hook-ask
    list — ping her before freezing anything Bluesim-ABI-shaped, and
    fold her asks into the same decision.
11. **SplitPorts:** authorize the compile + byte-identity + 8..128
    timing-sweep gate as a toolchain-session task; rejected
    alternatives (1)/(4)/(5) stay live until then.
12. **Orphan program:** WOrphanInst→error timing (standalone vs with
    CtxRed P0); route the GenSign defect (own filing vs #1061 comment);
    whether NEW-2/NEW-3 ride along.
13. **IExpr/IType landing:** the fork-CI 4-cell verdict consumption;
    the one-golden regold; forward rank-first Ord upstream?
14. **CtxRed/VTA sequencing:** does P1 ride the VTA branch or land just
    ahead; authorize the born-reduced-deriving experiment.
14a. **WrapField fix choice (04 §6):** field-name normalization vs
    join-after-WrapMethod vs dictionary CSE — the dictionary-lifting
    and evidence-digest work should build against the chosen lane.
14b. **Contract-files ↔ manifest unification (01 §1):** ratify that the
    3-phase flow proposal's contract files and the transitive manifest
    are one artifact family before the flow proposal circulates.
14c. **Own the session-context program (01 §3):** it is the named
    prerequisite of four lanes (parallelism rung 4, the LSP worker,
    bluehs persistence, the ATF ground-memo's conditional acceptance)
    and currently has no owner — assign one; it is likely the largest
    single internal refactor of the period.

## C. Ecosystem-facing proposals in waiting (your PR-policy gate)

15. **Reset-sequence RFC upstreaming** (changes main.v for every
    simulator; iverilog fully green; VCS validation pending a license).
16. **$random unification route:** Annex-N-everywhere (five engines
    byte-identical; collapses split goldens) and/or the BSV-level
    per-instance randomizer; seeded-first for any Verilator pitch.
17. **Open-packed DPI upstreaming (R3)** to Verilator issue 3198 +
    the MatX-inc/verilator write grant so the patch can re-land from
    the chat-delivered copy (custody item).
18. **Scheduler transpose to B-Lang-org** (#1087) and the ethmac
    keyword fix + verilator regression filings — all staged, one click
    when the policy hold clears.
19. **The compat features' route:** '0/'1 + deriving-via LANDED on the
    fork's main (04 §5); the remaining decision is the upstream route
    and timing.
19a. **Parser implementation choice (06 §2):** Megaparsec (the Aug 7
    decision, engagement-staffed) vs the LALR(1) port the lexer arc
    judged practical — reconcile before the parser rewrite hardens.
19b. **Touch-point tracing (06 §2):** absent from the Unison M1–M4 —
    deliberate sequencing or a dropped thread? Decide before terms are
    agreed.
20. **$finish #0 emission upstreaming** — weigh VCS validation first
    (golden churn ~13 re-records; behavioral improvement).

## D. Strategy (no lane records an answer)

21. **trs's ultimate home** (07 §4.1): side-tree forever, or an
    eventual upstream offering (tool suite vs backend)? The
    smaller-tools origin gap is now closed (10 §1); the strategy
    question remains. Two sharpenings from the cross-cut: (a) the
    artifact-graph RFC's "trs consumes bir nodes" reading quietly
    assumes trs is a first-class backend of the future bsc — decide
    whether BIR versioning is an internal or public contract; (b) the
    **monorepo insertion path is unowned** (07 §5): who designs the
    post-freeze rollout (release channel, build-rule changes, port-ABI
    non-impact proof), and is the post-freeze window (07 §5) the
    target?
21a. **Testsuite premise ownership:** is upstream acceptance of the
    Shake engine (staircase S4) an actual goal with an owner and
    timeline, or should planning assume fork-only (which flips the
    testsuite verdict to do-not-migrate and keeps DejaGNU + the S1
    tools)?
21b. **Divergence policy ratification:** adopt T9's operational form
    as the decision-of-record — any fork divergence must be pinned,
    declared in artifact identity, and carry an upstream exit plan —
    so future lanes inherit it rather than rediscovering it.
21c. **PR-hold scope:** does the 2026-08-23 hold apply uniformly, or
    can byte-neutral bug fixes (the transpose, ethmac keywords,
    verilator regression filings) proceed while policy is sorted?
22. **VCS engineering depth** (07 §4.3): how much investment the
    VCS-specific paths (trs shell under VCS, encrypted-IP flows,
    VCS-as-oracle CI seats) deserve. Includes confirming the
    transport reading of 02 §5: trs-shell exports are monomorphic at
    generation time, so mangled DPI should serve VCS — if a
    width-polymorphic shell boundary ever exists, VCS forces a VPI
    realization there.
23. **Issue-inventory identity questions** (the inventory's sec E —
    an upstream GitHub-identity roster matter): the BracketMaster
    account mapping; the mieszko account's affiliation dates; pre-2023
    scope — plus adopting the issue→design ownership map as a
    maintained artifact.
24. **KB process:** freeze the toolchain continuation draft (Codex's
    ratification-time ask); the internal Bazel-free generator harness
    (07 §5's ground-truth survey; details in the trs lane) is used as a
    standing gate while Codex's fail-closed fingerprinting conditions
    remain unadopted — accept the risk or fund the fix.

## E. Standing custody/infrastructure items

25. MatX-inc/verilator write grant (17); BENCH_ARCHIVE_TOKEN; the
    unpushed BVI-fallback proposal branch (needs a B-Lang-org push
    grant or git-am); the sibling winning-monorepo branch landing;
    matx-corpus reseal needs a matx-attached session.
26. **Meeting-record access (10 §7):** LARGELY RESOLVED — sessions
    running under Ravi's own credentials read the full notes,
    transcripts, and the coverage proposal (the credentialed crawls of
    2026-08-24); the service-identity restriction stands for
    unattended sessions. Remaining: manual capture for the Jul 22
    roadmap meeting (folder-verified to have no notes doc) and May 13
    "Formal Bluespec"; and the still-unmined transcripts per the
    digest's handoff block — the LSP, portfolio, and Aug 21 sync
    transcripts are mined; the PR-landscape session, the Jeff/Ravi
    series, and the Jul 10 / Jun 26 / Aug 3 details remain.
