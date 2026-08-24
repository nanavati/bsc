# 08 — Landing Order: The Cross-Lane Dependency DAG

What must land before what, and why — the composite ordering that keeps
individually-green lanes from composing into silent failures.

**Status:** v1.1 — 2026-08-24 (Claude, holistic review + cross-cut
reconciliation). This adopts, corrects, and extends Codex's index-draft
chain (bootstrap index, 2026-08-23 22:27 UTC), reconciled in §3 with
its 22:17 composite-order proposal, which orders N2/N4 oppositely.
The shared rationale stands: the
combined Gmail + 113-PR audit found silent schema-compatibility,
misbinding, cache-identity, X-policy, and oracle failures that
disappear when branches are reviewed alone. Individual lanes do not
claim product readiness ahead of their prerequisites.

## 1. The DAG

Nodes ordered; "→" = hard prerequisite. Status: L = landed/measured,
I = implemented not landed, D = designed only.

**N0. The closure/validity doctrine** (D; 04 §1) — the theory the
enforcement nodes implement. No code; must be written into the
coherence/ATF/CtxRed lanes' shared vocabulary (this book does that).

**N1. Format registry + transitive manifest** (D; 01 §2) — the root.
One tag registry (.bo/.ba/BIR/snap/plan/AOT/callback ABIs) with
compatible-vs-breaking rules and reject-unknown-semantic-fields
readers; the five-identity manifest attached to every durable artifact;
fail-closed strict modes. *Why first:* every audit-found composition
failure is an identity failure; PR-144/47 unbumped schema changes and
the AOT rev-26 callback-ABI reuse are live instances. Includes the
recertification set (PRs 47, 66, 67, 87, 144, 151, 152; rev-26).

**N2. Coherence + orphan enforcement + sealed ATF evidence** (N0→; 04)
— the stack #1033–#1038 (I, awaiting upstream review), GenSign fix (D),
use-site orphan rejection with the no-orphans class property (D),
sealed-family certificates + evidence digests into N1's manifests (D).
*Why before boundary work:* instance evidence IS ABI identity; every
port/encoding witness downstream keys on it.

**N3. Session context + run-local metadata discipline** (I/D; 01 §3)
— CompilationSession/QueryContext owning interner arenas, rule
snapshots, memos with three lifetimes; the IType/IExpr substrates land
under it. *Why here:* prerequisite for ladder rung 4, the LSP worker,
constructor-time ATF folding, and any persistent build worker; and the
ATF ground-memo (PR 93) is unsound without a scoped lifetime.

**N4. Canonical schedule artifact + BoundaryBinding/PortTree**
(N1→, soft N2 edge — see §3; D; 02 §2, 03) — one producer (bsc),
consumers validate; note 02 §2's "coherence-side enforcement first"
precondition binds N5's *certification*, not this artifact itself;
schedule digests; exported coordinates (auto-fire, alternatives);
final-name map; the contract(ba) total projection (persist
veriPortProps/true_ifc_ids). Carries the one-order compatibility rung.

**N5. SplitPorts restructure + semantic port properties** (N2,N4→;
I; 02 §2) — gated on compile + byte-identity + the timing sweep +
capability matrix; port-properties facts partitioned into
contract-vs-binding per schedule digest.

**N6. trs lifts: top bindings / auto-fire / dynamic scheduling**
(N1,N4→; L with conditions; 03 §R3.3–R3.5, 05) — binding manifests
replace salts; exported coordinates replace last-cut reconstruction;
pinned arm tables; the manifest/fail-closed honesty rung. STATUS
ADVANCE (2026-08-24): the #158-gating objection set is CLOSED and
pushed (REV-27 fail-closed callbacks; liveness + always-on audit +
unconditional trap + honest census; linkage fix; time-passes contract
— 05 §2); the recommended merge gate is a fresh full-corpus diffsweep
seal, and the N1-shaped recertification obligation stands.

**N7. Explicit initialization + soft-IP binding + mixed-state BVI
semantics** (N1,N4→; D/I; 02 §4, 05 §§3–4) — the X policy vector in
manifests; the reset-sequence contract (L on its branch); the BVI
fallback clause with binding map; the .ba graft seam; defined
divergences and 2-state islands scoped in certificates.

**N8. Exact codebook witnesses** (N2→; D; 02 §3) — assign_tags port +
differential fuzz gate; decoder/validator generated from one
fingerprinted witness; fingerprints into semantic identity.

**N9. Stable worker/query protocol** (N1,N3→; D; 06 §4) — the
LSP/bluehs/test-orchestrator surface; versioned action-keyed replies;
authority/freshness classes.

## 2. Corrections and extensions to the proposed chain

- **N0 added.** The doctrine is what makes N2's enforcement principled
  rather than ad hoc; stating it once prevents three divergent
  vocabularies.
- **N3 generalized** from "run-local IType/IExpr metadata discipline"
  to the full session-context program — the same demand appears in four
  lanes and should be built once.
- **Parallel tracks made explicit.** Three lines are independent of
  N1–N9 and should not queue behind them: (P1) the Shake driver +
  cabalization (artifact-graph rungs 1–2) — enables everything, blocks
  on nothing, and now carries upstream's own momentum: the 3-phase
  compile split + contract files decision and the prioritized Cabal
  migration (10 §1) ride P1, with contract files unified with N1's
  manifests (01 §1) and the staged-flow mechanics already live as
  upstream PRs 1092–1094 (-elab-only ruled transitional); (P2) the
  reset-sequence/oracle-harness arc and the verilator fix upstreaming
  — simulation-contract work with its own gates, now at its final
  branch-local ledger with the hardware-model-line ruling and the
  disable-at-$finish emission landed (05 §4); (P3) CtxRed P0/P1 + born-reduced deriving — front-end identity
  work whose only coupling is N2's vocabulary; VTA lands after P1(CtxRed).
  Scheduling RFC steps 1–3 run parallel after N4 exists in draft form
  (the footprint artifact IS part of N4; the tour's resources/uses
  scheduler patch folds into step 1 per 03 §R3.7).
- **Per-rung trs PRs continue** during all of this (DECISION, Ravi):
  the DAG gates *productization claims and cross-lane composition*,
  not the measured-campaign cadence. The cross-cut analysis sharpens
  this into a **two-tier landing rule** (PROPOSAL, NEEDS-RAVI):
  upstream-facing semantics-preserving work (transposes, fixes,
  analyses) lands on its own evidence; anything *serializing new schema
  or claiming cross-engine identity* (dynsched .ba/BIR fields,
  port-property metadata, BVI contracts, codebook witnesses, toplift
  salts) waits for N1. This matches the audit's rationale without
  freezing delivery.
- **Testsuite migration** is a consumer of P1's rung 2 plus N1's
  verdict classes, on the upstream-landed premise only.

## 3. The critical path to a coherent product

GenSign-fix → N1 → {N2 ∥ N4} → N5 → N7 → N8 → N9, with N0/N3 as
cross-cutting enablers and P1–P3 in parallel. The single
highest-leverage unbuilt artifact is N1's manifest: it is named as the
missing piece by nine independent reviews, it retroactively soundifies
already-landed work (the recertification set), and every later node
writes into it.

Corrections adopted from the cross-cut DAG analysis (v1.1):

- **N2 and N4 are parallel after N1, both mandatory before N5.** The
  source chain exists in two versions with opposite N2/N4 orderings
  (Codex's index-draft chain vs its composite-order proposal); the
  corpus gives no hard edge between them — only a soft N2→N4
  simplification (specialization keys hash dictionary trees *because*
  bsc classes are not coherent; a landed coherence stack may simplify
  N4's keys). Any citation of "the" chain must say which version.
- **A layer 0 of dependency-free starts exists and should start now:**
  the GenSign expanded-head fix (04 — Codex's own "independently and
  first", omitted from its chain); the determinism substrate (01 §6);
  the orchestrator-neutral testsuite items (01 §5); and the three
  censuses (cacheability; urgency/execution divergence — runs on
  today's scheduler; used-set/flavor-diff). The two cheapest
  de-risking moves are N1's tag registry (no dependencies; converts
  N6's retrofit debts into mechanical checks) and the censuses (each
  turns a contested ordering claim into a number).
- **N6 is retrospective**: the chain's function there is a
  *recertification* order over already-landed work, not a landing
  order.
- **N7 splits by maturity**: the X-policy/ValidateBits piece is
  design-complete and deliberately independent (05 §4 — do not force
  it to co-land with soft-IP binding); the soft-IP piece is
  design-plus-old-base-implementation; the BVI-via-Verilator piece is
  implemented with its objection set as the acceptance bar.
- **The binding constraint is review capacity, not design order**: the
  freeze, the PR hold, and the idle upstream stack make early nodes
  review-bound (07 §4.4, 09 A.3).

## 4. Lane → node map

| Lane (KB draft / branch) | Node(s) |
|---|---|
| artifact-graph RFC + testsuite-after-shake | N1, P1, verdict classes |
| polymorphic-scheduling RFC | N4 + scheduling steps 1–8 |
| typeclass coherence (+orphans) | N0, N2 |
| ATF rewrite rules; IType; IExpr/notes | N0, N2, N3 |
| CtxRed retirement; VTA; deriving | P3 (N2-coupled) |
| solver strategy | N2 (evidence), 05 (X analysis), flag-day rules |
| SplitPorts; semantic port properties | N5 |
| HuffmanBits | N8 |
| BVI fallback/soft-IP; open-packed DPI | N7, N4 (ForeignABI in N1) |
| BVI-via-Verilator; verilator integration; reset sequence | P2, N7 |
| trs full-AOT; toplift; dynsched | N6 + per-rung track |
| bluehs; LSP | N9 (N3-gated) |
| pattern-match; port props diagnostics | verdict/observability rules in N1 |
| issue inventory | the ownership map feeding this table |

## 5. NEEDS-RAVI

- Ratify this DAG (or amend) as the composite gate — in particular that
  N1 is funded/sequenced first and that the recertification set is
  scheduled.
- Record it in the KB bootstrap index (Codex's ask) — done by this
  review's KB deposit.
- Priority between N5/N6/N7 once N4 exists — they are parallel in
  principle; staffing makes them serial in practice.
