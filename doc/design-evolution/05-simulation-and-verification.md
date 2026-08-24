# 05 — Simulation and Verification: trs, X, Oracles, and Coverage

The simulator program's destination: the trs architecture, the X
semantics program, the reset and finish contracts, the oracle
discipline, the coverage program, and Bluesim's designed role.

**Status:** v2.0 — 2026-08-24 (Claude). Design only; campaign status,
gates, and sequencing live in the KB lanes; provenance in the
meeting-notes digest — all outside this set.

## 1. The trs architecture (DECISIONS of record)

1. **Frozen-bsc side-tree**: trs lives beside a frozen compiler
   surface — all trs churn in added side files, the exporter a
   side-built tool with shadow modules for the few behavior deltas,
   serialized-format extensions deleted in favor of in-memory flows
   (artifacts return to byte-stock), and general compiler improvements
   flowing as ordinary small upstream-shaped changes. *Why:* the fork
   surface stays enumerable and the simulator's evolution stops
   holding the compiler's identity hostage.
2. **Flavor transparency**: trs consumes whatever artifact flavor it
   is given; the exporter normalizes to one BIR semantics; a
   dual-flavor seal chains the reference oracle onto the other
   flavor; refusals are loud, per-construct, and ledgered.
3. **BVI last-resort ladder** (02 §4).
4. **Smaller tools**: a porcelain over durable artifact boundaries —
   export / plan / emit / link / run / shell; a stage is a separate
   tool exactly when its boundary artifact earns parallelism, caching,
   inspection, or a second consumer; interpreter and compiled tiers
   share one process (the lockstep self-check shares the arena).
   Language boundary = semantic boundary: Haskell where trs must agree
   with bsc *by reuse* (exactly the exporter), Rust where trs must win
   *by measurement* (it also drives LLVM generation directly — no
   second compile through another toolchain, and the runtime and
   codegen share one implementation language).
5. **Hierarchical all the way down**: per-module(-type) artifacts plus
   a thin design-level superstructure; near-linear superstructure
   passes with tripwires. Loop re-rolling — pattern-matching
   elaboration output to merge identically-stamped structures — is the
   designed answer to replicated-grid scale.
6. **Separate compilation just works**: per-module fragments carry two
   hashes (interface/body); dependents key on interface only;
   design-level derivation moves to link; opt-in link-time re-fusion
   re-accepts its costs knowingly.
7. **Module-level replaceability + trs shell**: fragments are
   standalone-linkable products carrying the full port contract; the
   shell speaks the long-established generated-Verilog port protocol
   with the executor swapped; the boundary is DPI (4-state from birth:
   the value channel carries the planned X-taint mask), VPI reserved
   for introspection.
8. **Engine-agnostic module boundary + fusion regions**: compiled,
   interpreted, and verilated-leaf implementations interchange per
   instance behind one slot ABI; the proportionality rule —
   interpreter cost proportional to the frontier, never global; a
   fully-compiled design is one region with zero interpreter presence
   per cycle.

Standing doctrine: Bluesim remains production until replacement is
*proven* (§4's certificates plus 01's identity discipline); the
campaign method itself — census → registered predictions → fix →
scored ledger → multi-witness seal — is design method, not process
trivia: null results don't land, and the bar of record is the fastest
opponent's wall. Measured lever conclusions that shape the design
(corpus-conditional by construction, 07): dynamic residue is the
universal lever ("nothing walked per cycle"); activity gating is
opt-in (null on active cores, real on large idle subsystems);
vectorization pays only as across-instance SIMD on wide replicated
shapes; cache *tuning* is off the menu but structural locality is on
it.

## 2. The X program

One doctrine, five pieces:

1. **Reference semantics**: possible-worlds concretization of
   one-rule-at-a-time execution over demonic X resolutions. The core
   criterion (Ravi): **X must never make the event set of an execution
   uncertain** — occurrence-doubt is the atomicity peril; value-doubt
   riding a fixed event set is per-bit representable. Neutral
   equivalents decide reducibility (register writes benign; FIFO
   ops/$display/$finish/rule-inhibition irreducible; neutrality is
   relative to the observation algebra). OPEN inside this piece, with
   both positions on record: whether an unconditional write of an
   X-valued payload differs from a conditional write with X folded
   into the value — the condition-X-breaks-atomicity view ("the whole
   rule goes to X; the value is tracing the invariant break when it
   happens") versus the value-X/condition-X-equivalence view. The
   agreed resolution vehicle is a formal write-up with a soundness
   argument.
2. **Engine division of labor** (DECISION): X lives in trs only —
   two-state mode remains (the benchmarking configuration); 3-state
   (0/1/X; Z only at the boundary) is the reference semantics
   everywhere else; Bluesim is never retrofitted with Kleene logic —
   it is the designated-world evaluator and, after the reset
   bootstrap, the Monte-Carlo initialization sampler.
3. **The ladder**: fail-stop when taint reaches an irreducible sink;
   then poison the influence cone; then refuse to merge a live shared
   condition — named unknowns, world forking, per-bit value+mask taint
   with a symbolic layer; concrete backing stays the
   designated-world fill so output remains byte-identical to the
   oracle (parity from the concrete plane, soundness from the taint
   plane). Atomicity arguments remove timing uncertainty, not
   dataflow taint — the taint plane, not written-flag ghosts, is the
   proof engine.
4. **The certificate program** (DECISION-flavored): replacing the
   oracle requires *proving* X unnecessary — dynamic per-run
   certificates (X-freedom telemetry as a replacement gate), static
   taint reachability over the schedule graph bounded by the reset
   window, and the Monte-Carlo sweep as falsifier and
   prover-validator. Any foreign Verilog voids the proof; the
   artifact graft (02 §4) restores it. Verilated foreign models are
   permanently two-state islands; design-wide X claims scope around
   them or refuse the boundary.
5. **Boundary checking now**: ValidateBits — an is-unknown primitive
   and an observation primitive, validate/strictValidate, the
   monotone expression-plane theorem, fail-closed caseification inside
   marked cones, the **X policy vector** (state init / reset bootstrap
   / foreign initial blocks / boundary coercion) recorded in manifests
   and certificates, and derivation coherence (deriving ValidateBits
   without co-derived Bits is an error; the roundtrip law is
   property-tested). This piece must not gate on the longer program.

## 3. The reset and finish contracts

The **reset-sequence contract**: the observable window starts at each
domain's first post-deassert edge; the sequence exercises the real
reset tree with no reliance on initial blocks or X-edges; the
assert/deassert choreography is architectural, documented, and shared
verbatim by harness and primitives; determinism is argued per
transition class. The **hardware-model line** (DECISION, Ravi, 00 §2)
bounds all of it: reset synchronizers and their kin are real hardware
— simulator-emulation gaps (a two-state engine cannot see a
four-state X→asserted edge) are closed by per-test simulator
configuration or honest expected-failure markers, never by teaching
primitives simulation-only behavior; the harness's own startup pulse
is testbench choreography and stays. Global four-state-initialization
emulation over-approximates by construction (a derived signal
initializing high registers a spurious edge) — which is *why* the
per-test knob is the design, not a concession.

The **finish clause** of the observable-event contract is stated and
emitted (03 §2): displays of a timestep flush before $finish commits;
post-finish statements never execute — realized structurally in the
generated Verilog rather than accommodated per simulator. $random
unification rides the same contract family: one LRM-specified
generator everywhere plus a source-level per-instance randomizer
compose, and collapse split goldens; seeded-first is the portable
form.

## 4. The oracle discipline

Correctness is established by differential comparison against
designated oracles plus recorded witnesses — never by review or the
absence of warnings (T7). The oracle lattice (Bluesim ↔ trs ↔
event-driven open-source simulators ↔ commercial simulators) with
pinned divergence classes replaces "match Verilog" — ill-posed, since
the LRM disagrees with itself across engines — with per-contract,
per-oracle witnesses. Oracle succession is per-fixture; stored
goldens are terminal; a second pinned engine and
netlist-under-simulator runs serve as drift detectors. Because
byte-parity gates cannot see engine downgrades, every claim also
carries engine telemetry and fail-closed strict modes (01 §2).
Foreign-simulator pins converge to stock releases — a pin is a bridge,
not a home — with fixes upstreamed and the pinned fork kept as an
emergency vehicle.

## 5. Bluesim's designed role

Bluesim remains: the byte-parity reference and designated-world
evaluator; the Monte-Carlo initialization sampler after the reset
bootstrap; the semantics oracle the dual-flavor seal chains onto the
other flavor. Bluesim gains: the reset bootstrap (pattern knob), port
properties in its interface artifacts, per-module staged codegen (as
graph nodes), FST dump support, and — candidate, not committed — a
synchronous kernel stepping API (inline single-stepping without the
helper thread; motivated by model fuzzing, which is also a consumer
voice for future hook design). Bluesim does not gain: Kleene X, new
kernel surface beyond the deliberately-weighed poke extension (06),
or schedule-model changes ahead of the one-order migration. Kernel
ABI evolution is coordinated with all stakeholders before any freeze
(08).

## 6. The coverage program

Thesis: **bsc instruments coverage because it is the last tool that
still sees design meaning** — default output renders rules as
always-executing continuous assignments, so standard line/branch/FSM
coverage saturates meaninglessly, and instrumenting the generated
Verilog (any downstream tool's coverage mode) inherits the erasure.
Emission is standard cover constructs into the standard collection
stack, so the existing merge/exclusion/trending/closure workflow is
inherited, not rebuilt.

The instrument set: **rule coverage** (can-fire/will-fire); **conflict
coverage** (can-fire and not will-fire — lost arbitration, which has
no RTL-coverage analog); state/enable coverage; **mux-arm coverage
with writing-rule attribution**; **select-point coverage** harvested
from the evaluator's residue (anything surviving partial evaluation is
dynamic by construction; guard conjuncts are captured *before*
boolean simplification — a pass-ordering constraint that is cheap
early and expensive to retrofit); **covergroups generated from the
type dictionary** (per-constructor bins, payload bins conditioned on
tag, ready/enable-gated sampling — guard-correct by construction;
illegal encodings become generated checks instead of manual
exclusions, turning closure labor into a bug detector); and
model-side functional coverage. Deliberately deferred: rule-body line
coverage in the reference simulator (its exclusive residual — line
granularity inside branch-free dataflow — is something no
branch-coverage regime measures meaningfully).

Identity discipline: points are keyed by **structural identity** (rule
name + instance path + ordinal + expression shape) and aggregated
across instances; source position is a display attribute only. That
deliberately splits the coverage signal (buildable now) from position
fidelity through unfolding — a separate substrate whose consumer set
exceeds coverage (go-to-source debug, warnings, mux-report
readability; 06 §3) — so accumulated coverage survives position
improvements and upgrades retroactively. Noise control is designed
in: a static always-fire tier excluded from denominators at emission,
an empirical non-discriminating tier, and the headline metric
"N points, M informative, K covered."

## 7. Pointers

Mechanism and evidence: the trs design documents and full-AOT lane;
the BVI-via-Verilator design; the ValidateBits design; the
reset-sequence RFC; the verilator-integration lane; the coverage
proposal; the solver-strategy record. Indexed in the KB; open design
decisions in 08.

## 8. RESOLUTIONS and OPEN questions

- RESOLUTION: the X doctrine is one program with five pieces;
  boundary checking does not gate on the certificate program.
- RESOLUTION: taint, not atomicity ghosts, is the X proof engine.
- RESOLUTION: the fallback clause and the simulator graft are one
  design (02 §4); X-provability is restored through it.
- OPEN: the value-X vs condition-X question (§2.1) — the write-up
  with soundness argument decides it.
- OPEN: the finish/observable-event contract's remaining clauses;
  the $random unification route.
- OPEN: ValidateBits residuals (completeness bound; non-blessed
  config diagnostics; unknown-arm spelling; blessed X-lane defaults).
- OPEN: the coverage proposal's design questions (register-mux
  rendered form; SVA cover vs covergroup emission; guard-conjunct
  pass placement; rule-body-depth interest).
- OPEN: whether an ecosystem-visible primitive may have its reference
  semantics defined by 3-state trs, or the completeness bound is
  pinned in a simulator-independent spec.
