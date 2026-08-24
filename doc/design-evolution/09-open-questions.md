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
   (Monday's meeting).
4. **The solver policy ceiling (04 §3):** ratify "complete where
   decidable, axiomatic where not, heuristic never," as amended to
   "no uncheckable or non-monotone acceptance," as the permanent
   acceptance-frontier rule — plus the scheduler-vs-typechecker solver
   ownership split and flag-day rule.
5. **One-order compatibility rung (03 §R3.1):** approve running the
   urgency/execution divergence census (today's scheduler; testsuite +
   a large internal corpus, 07) and the named-rung/format-generation
   treatment of the break.

## B. Design ratifications waiting (single-lane, ready)

6. **HuffmanBits adoption gate:** (a) exact assign_tags port +
   differential fuzz vs Rust VARIANT_TAGS (recommended; Codex ACK) vs
   (b) canonicalize both sides (flag-day). Also: share the study's
   companion artifacts.
7. **BVI fallback (02 §4):** ratify the structural binding design with
   the review conditions as v1 scope; decide the soft-IP
   implementation's rebase route.
8. **ValidateBits residuals:** Q1 (completeness bound), Q3 (non-blessed
   config: warn vs error; lean warn-once-per-module), Q4 (reserve the
   unknown-arm spelling), Q6 (X-lane defaults; name the blessed
   two-knob configuration); the X-payload doctrine question (leans
   "payload X flows"); final D7-prose alignment.
9. **BVI-via-Verilator:** Q4 strict mode (recommendation on record:
   ratify strict); pick and provision the pinned Verilator (the fork
   release from the fixed tip); observability tier 2; landing the
   branch into the stack.
10. **bluehs sim scripting:** ratify the v1 bar (parity, no poke) and
    the first consumer (isolated-worker lockstep driver); the
    poke/deposit kernel-extension question.
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
19. **The compat features' route:** '0/'1 + deriving-via as a trs stack
    rung vs upstream PRs first.
20. **$finish #0 emission upstreaming** — weigh VCS validation first
    (golden churn ~13 re-records; behavioral improvement).

## D. Strategy (no lane records an answer)

21. **trs's ultimate home** (07 §4.1): side-tree forever, or an
    eventual upstream offering (tool suite vs backend)? The
    smaller-tools origin gap is now closed (10 §1); the strategy
    question remains.
22. **VCS engineering depth** (07 §4.3): how much investment the
    VCS-specific paths (trs shell under VCS, encrypted-IP flows,
    VCS-as-oracle CI seats) deserve.
23. **Issue-inventory identity questions** (sec E): BracketMaster
    mapping; mieszko's affiliation dates; pre-2023 scope — plus
    adopting the issue→design ownership map as a maintained artifact.
24. **KB process:** freeze the toolchain continuation draft (Codex's
    ratification-time ask); the monorepo Bazel-free generator harness
    is used as a standing gate while Codex's fail-closed fingerprinting
    conditions remain unadopted — accept the risk or fund the fix.

## E. Standing custody/infrastructure items

25. MatX-inc/verilator write grant (17); BENCH_ARCHIVE_TOKEN; the
    unpushed BVI-fallback proposal branch (needs a B-Lang-org push
    grant or git-am); the sibling winning-monorepo branch landing;
    matx-corpus reseal needs a matx-attached session.
26. **Meeting-record access (10 §7):** share the coverage proposal
    document and (optionally) the Gemini meeting-notes folder with the
    agent service identity ai.agents@matx.com — the crawl could read
    only the summary emails, not the full notes; the coverage proposal
    was unreachable entirely. Manual capture needed for the Jul 22
    roadmap meeting and May 13 "Formal Bluespec" (no auto-notes exist).
