# 05 — Simulation and Verification: trs, Bluesim, Oracles, and X

The simulator program: trs's architecture doctrine and campaign, the
BVI execution path, the X semantics program, the oracle discipline,
and Bluesim's role.

**Status:** v1.0 — 2026-08-24 (Claude, holistic review). Labels: FACT /
DECISION / PROPOSAL / RESOLUTION / NEEDS-RAVI.

## 1. The trs doctrine (DECISIONS of record, Ravi 2026-08-22/23)

1. **Frozen-bsc side-tree**: trs lives in the MatX bsc repo with every
   upstream-tracked bsc file frozen at main; all trs churn in added
   side files; CI tripwire that the diff outside side dirs is empty;
   the exporter becomes a side-built tool (trs-bir) with shadow modules
   for the few behavior deltas; the dynsched .ba schema extension and
   Flags-record .ba growth are deleted (.ba returns to byte-stock);
   orphan bsc improvements become tiny ordinary PRs. Supersedes the
   stack's *shape*; deferred — per-rung PRs continue meanwhile.
2. **Flavor transparency**: trs eats whatever .ba it is given
   (Verilog-flavored default at MatX, Bluesim-flavored outside); the
   exporter normalizes to one BIR semantics; the **dual-flavor seal**
   chains the Bluesim oracle onto the Verilog flavor; refusals are
   loud, per-construct, and on a burn-down ledger converging to
   ~{inout}. First restructure measurement: the flavor-diff census.
3. **BVI last-resort ladder** (see 02 §4).
4. **Smaller tools**: the `trs` porcelain over durable artifact
   boundaries — trs-bir / plan / emit / ld / run / shell; a stage is a
   separate tool exactly when its boundary artifact earns parallelism,
   caching, inspection, or a second consumer; interp+compiled stay one
   process (the lockstep selfcheck shares the arena); the orchestrator
   is Rust. Language boundary = semantic boundary: Haskell where trs
   must agree with bsc *by reuse* (exactly trs-bir), Rust where trs
   must win *by measurement*.
5. **Hierarchical all the way down**: per-module(-type) artifacts plus
   a thin design-level superstructure; near-linear superstructure
   passes with tripwires.
6. **Separate compilation just works**: per-module fragments carry two
   hashes (interface/body); dependents key on interface only; design-
   level derivation moves to link; opt-in -O link re-fuses (plan-layer,
   not ThinLTO), costs re-accepted knowingly.
7. **Module-level .ba is the replaceable unit + trs shell**: fragments
   are standalone-linkable products carrying the full port contract;
   trs shell speaks the 26-year generated-.v port protocol with the
   executor swapped; boundary = DPI (4-state from birth: bval carries
   the planned X-taint mask), VPI reserved for introspection.
8. **Engine-agnostic module boundary + fusion regions**: compiled,
   interpreted, and verilated-leaf implementations interchangeable per
   instance behind one slot ABI; the proportionality rule — interpreter
   cost proportional to the frontier, never global; a fully-compiled
   design is one region with zero interpreter presence per cycle
   (TRS_PROF zero-tick tripwire).
9. **Realization plan**: emit sharding → boot-tax re-measure → the one
   BIR_VERSION break (fragments + hashes + content_hash + flavor
   census, with a dual-path period) → side-tree → porcelain split →
   -O re-fuse + trs shell.

DECISION (standing): Bluesim remains production; trs is the
next-generation simulator being *proven*. The campaign method — census
→ registered predictions → fix → scored ledger → multi-witness seal →
per-rung PR — is itself doctrine.

## 2. Campaign state and lever verdicts (FACTs)

All-AOT invariant holds (1003/0 seals; engines all-aot). Toooba at
Verilator parity (24% fewer instructions; the D1 differential is the
equalizer; store-side EN sweep is the named next lever); link time is
the named scaling wall (LLVM passes on one 25M-insn module; sharding-
as-trs-emit is the doctrine answer). MatX corpus: 136 tests byte-exact
all-AOT; zero known parity divergences; wire-heavy benches 2.4–6.6×
FASTER than Bluesim -O3; unit tests ~10× end-to-end (boot 4–6ms vs
bluetcl 55–70ms). Lever verdicts: dynamic residue is the universal
lever ("nothing walked per cycle"); activity gating opt-in (null on
active cores; fits large idle subsystems); vectorization dead on Flute
shapes, census-gated upside as across-instance SIMD on MatX shapes;
RunCore-for-BDPI dead for perf; cache *tuning* off the menu but
structural locality on it. Performance claims stay corpus-conditional
(the Flute-vs-MatX profile inversion is the deepest external-vs-MatX
fact); the bar of record is the fastest opponent's wall.

RESOLUTION — **identity and honesty rungs gate productization**: the
adopted-in-lane manifest/fail-closed rung (requested-vs-actual engine,
fallback reasons, digest-verified launchers, conditional determinism
seal with per-leg stdout digests) plus the five open PR #158 objections
(MethValue liveness + fail-open interp; alt-guard liveness and the
circular census; AOT rev-26 callback-ABI reuse; time-passes globality;
chunked-AOT symbol collision) are treated as a first-class workstream,
not review noise. "Parity of record" language stands for measurement;
*readiness* claims wait on the registry/manifest prerequisites (08).

## 3. BVI execution (as built) and its successor path

BVI-via-Verilator v5 (as built): shadow-vector execution behind the
prim ABI; exactness theorem with export-time refusals as boundary
conditions; verilation is a build step (run side load-only); compiled
by default; census endpoint reached (residue = 5×Inout permanent +
mesa); defined divergences pinned, never silent. Deployment: pinned
Verilator (the fork release cut from the fixed tip — stock 5.050
carries a material $signed-slice miscompile); floor = --timing
capability; re-run the r3 battery on any pin change; long-term posture
converges to stock upstream with the fork as an emergency vehicle.
Oracle succession is per-fixture: iverilog while IP compiles under it;
**VCS designated high-SV successor** (test-time only; "VCS incoherent
as an engine" unaffected); netlist-under-Verilator and a second pinned
Verilator as drift detectors; stored goldens terminal. Open in-lane:
strict-mode ratification (Q4; recommendation on record: ratify strict),
--bvi-model wiring, landing into the stack, pin provisioning,
observability tiers. Codex's identity objections (load-only class
pointer is last-build-wins, not immutably pinned; adapter protocol;
argv contract; init side effects at build; mixed two-state islands)
fold into the manifest workstream.

## 4. The X program (RESOLUTION: one doctrine, five pieces)

The corpus contains one coherent X doctrine spread across four lanes;
stated once:

1. **Reference semantics**: possible-worlds concretization of
   one-rule-at-a-time execution over demonic X resolutions. The core
   criterion (Ravi): **X must never make the event set of an execution
   uncertain** — occurrence-doubt is the atomicity peril; value-doubt
   riding a fixed event set is per-bit representable. Neutral
   equivalents decide reducibility (register writes benign; FIFO
   ops/$display/$finish/rule-inhibition irreducible; neutrality is
   relative to the observation algebra).
2. **Engine division of labor** (DECISION): X lives in trs only —
   two-state mode remains (the vs-Verilator benchmarking config);
   3-state (0/1/X; Z only at the boundary, tentative) is the reference
   semantics everywhere else; Bluesim is never retrofitted with Kleene
   — it is the designated-world evaluator (AA) and, after the reset
   bootstrap, the Monte-Carlo init sampler.
3. **The ladder**: v0 fail-stop when taint reaches an irreducible
   sink; v1 poison the influence cone; v2 refuse to merge a live shared
   condition — named unknowns, world forking, per-bit value+mask taint
   with a symbolic layer; concrete backing stays AA so trs output
   remains byte-identical to Bluesim (parity from the concrete plane,
   soundness from the taint plane).
4. **The certificate program** (DECISION-flavored, Ravi): replacing
   Bluesim requires *proving* X unnecessary — dynamic per-run
   certificates (x_free telemetry as a replacement gate), static taint
   reachability over the BIR schedule graph bounded by the reset
   window, and the Monte-Carlo sweep as falsifier and prover-validator.
   Any Verilog voids the proof; the .ba graft (02 §4) restores it.
   Verilated BVI models are permanently two-state islands; design-wide
   X claims scope around them or refuse the boundary.
5. **Boundary checking now**: ValidateBits — primIsUnknown +
   primObserved, validate/strictValidate, the monotone expression-plane
   theorem, fail-closed caseification inside marked cones, the
   **X policy vector** (state init / reset bootstrap / foreign initial
   blocks / boundary coercion) recorded in manifests and certificates,
   and derivation coherence (deriving ValidateBits without co-derived
   Bits is an error; roundtrip law property-tested). This is the
   near-term bug-finding face of the roadmap and Erez's recorded
   feature ask; it must not gate on the longer program.

The reset-sequence RFC is the substrate contract: the observable
window starts at each domain's first post-deassert edge; the sequence
exercises the real reset tree with no reliance on initial blocks or
X-edges; assert level at 0 / posedge under reset / pulse / release;
determinism argued per transition class. It changes main.v (every
simulator) — the ecosystem-facing proposal is Ravi's to make. The
$random finding rides along: three generators today (Bluesim glibc!,
LRM Annex N, Verilator xorshift); Annex-N-everywhere plus a BSV-level
per-instance randomizer compose and would collapse split goldens;
seeded-first for any upstream Verilator pitch.

## 5. Bluesim's role, stated plainly

Bluesim remains: the production simulator until trs's proof program
and identity rungs land; the reference for byte parity and the
designated-world evaluator; the Monte-Carlo sampler after the
bootstrap change; the semantics oracle the dual-flavor seal chains
onto the Verilog flavor. Bluesim gains: the reset bootstrap (pattern
knob), port properties in .bo, staged-flow per-module codegen (as
artifact-graph nodes). Bluesim does not gain: Kleene X, new kernel
surface beyond the possible poke extension (06), or schedule-model
changes ahead of the one-order migration.

## 6. Lane pointers

"KB: trs full-AOT push" (doctrine, ledger, reviews); "KB: trs top-level
lifts + G0129"; "KB: BVI-via-Verilator design (trs)"; "KB: bsc
verilator integration" (reset/finish/two-state-z arcs); "KB: verilator
open packed DPI"; "KB: bsc X-safe ValidateBits design"; "KB: bsc solver
strategy" (X-analysis consumers); doc/RFC-simulation-reset-sequence.md;
src/trs docs; MatX PRs #108–#158.

## 7. NEEDS-RAVI (rolled up in 09)

- The finish-instant/event contract (with 03).
- BVI Q4 strict-mode ratification; pin provisioning; observability
  tier 2; landing the BVI branch into the stack.
- $random unification route (Annex-N-everywhere and/or per-instance
  randomizer); reset-sequence RFC upstreaming.
- The compat commit ('0/'1 + deriving-via) landing route: stack rung
  vs upstream PRs.
- X-payload doctrine question (does writing an X payload X the rule?
  doctrine leans no); ValidateBits Q1/Q3/Q6 residuals.
- Sibling-branch landing; BENCH_ARCHIVE_TOKEN; the PR #108–#158 review
  program itself (open with zero review comments).
