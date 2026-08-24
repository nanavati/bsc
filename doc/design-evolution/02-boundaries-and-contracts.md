# 02 — Boundaries and Contracts

The semantic/physical split and everything that binds at a boundary:
contracts as values, BVI in all its forms, the port ABI and its
witnesses, instance-specific synthesis, and the retirement of
genC/genVerilog.

**Status:** v1.0 — 2026-08-24 (Claude, holistic review). Mechanism
homes: RFC-bsc-artifact-graph.md §§7–10, 13; post-genwrap-compiler.md
(July 2026); the KB lanes named in §8. Labels: FACT / DECISION /
PROPOSAL / RESOLUTION / NEEDS-RAVI.

## 1. The split, restated once

Every synthesized boundary factors into a **semantic contract**
(IfcContract: interface types, method-level scheduling projection,
clock/reset *domain* structure and crossing promises, ready/enabled
promises) consumed by parent elaboration and scheduling, and a
**physical realization** (BoundaryBinding: port names, widths, roles,
sharing, encodings, clock/reset *port* bindings) consumed by netlist
composition. The .ba is the witness that connects them; VModInfo is
their materialized join. Licenses discharge every collapse in the
mapping from the semantic half. Same-cycle combinationally-bisimilar
re-encodings are physical freedom; latency changes are a different
semantic contract. Binding is two-stage: elaboration-time
(name → semantic contract) and link-time (instance → realization),
with vseg/vlink completing backend symmetry so any conforming
realization substitutes at link without parent recompilation. A20
governs throughout.

## 2. The port ABI needs a single owner (RESOLUTION)

Port layout is today defined independently by GenWrap/SplitPorts, the
BVI port table, trs export paths (which hard-code method port zero),
top-level lifting, and final Verilog identifier legalization — and the
orphan-mislink suite proved the failure mode is real hardware
corruption with zero diagnostics (five demonstrated silent mislinks;
same-name same-width reversed-lane ports; import-graph-dependent
pinouts; the GenSign synonym-omission companion defect).

RESOLUTION — one canonical **BoundaryBinding/PortTree** owns the
physical ABI: leaf identities and order, final names and the rename
map (through PR-42-style legalization — candidate names are not
authoritative), widths, roles, sharing classes, zero-width behavior,
clock/reset ports, and the committed Bits/SplitPorts/WrapPorts
*evidence* that produced the layout. Everything else (semantic port
properties, waveform correlation, trs binding, BVI fallback
conformance, LSP touch-points) consumes it. Preconditions, in order:

1. **Coherence-side enforcement first** (see 04): no-orphans class
   property on Bits/SplitPorts/WrapField/WrapMethod/WrapPorts; use-site
   orphan rejection; the GenSign expanded-head fix ("fix it
   independently and first" — Codex; RESOLUTION: agreed).
2. **SplitPorts restructure gate.** The tuples-all-the-way-down
   restructure (PortsOf mirrors the type; PairPorts collapse; flat
   ATTuple retained at ASyntax) is IMPLEMENTED BUT NEVER COMPILED
   (FACT). Gate before ratification: compile; byte-identical Verilog on
   the four named falsifier areas; the 8..128-field timing sweep (the
   O(n²) question is open and unmeasured); property tests for the
   leaf-order invariant (checkPortNames counts, it does not order —
   and orphan case 4 shows order divergence links cleanly); a backend
   capability matrix (trs, BVI, SAL/lambda paths) before certifying the
   serialized ABI change; schema bump per 01.
3. **Semantic port properties** (PRs #1059/#1060) partition per the
   review: structural role facts may live in IfcContract; rule-
   liveness, arbitration, EN-fold, and dropped-arm facts belong to one
   completed schedule and live in BoundaryBinding keyed by schedule
   digest; under SchedAlt only the intersection across legal arms is
   contract material. Complement folds must state their two-state
   domain (X policy tag). One canonical mux/binding plan is shared by
   lowering and analysis (T3). The default flip waits for the
   vtest-enabled goldens and the clean capability-visible suite.

## 3. Encodings are ABI: the codebook witness (RESOLUTION)

The HuffmanBits result generalizes: **width agreement does not imply
encoding agreement**, and the codebook policy (merge order,
tie-breaking, edge labeling) is ABI. The width theorem (root height =
ceil(log2 Σ 2^p_i)) makes generic deriving possible — only the width
must be type-level; tags are elaboration values that partially evaluate
away — and retires the repo's impossibility comments.

RESOLUTION: adopt Codex's "one versioned witness" frame — for each
encoding-owning instance, generate pack, decode, and validate from one
fingerprinted codebook witness; the fingerprint joins semantic/
specialization identity wherever packed values cross a package,
simulator, trace decoder, or cache boundary; invalid/unknown decode
semantics are specified (fail closed; unpack stays total but never
implies validity — ValidateBits is the validity oracle). Adoption gate
recommendation stands: **(a) port assign_tags exactly (S1–S7) with a
differential fuzz gate against Rust VARIANT_TAGS** (the roundtrip
attribute is insufficient); canonicalization (b) remains a later
coordinated flag-day. Migration must be coherence-safe: compile the
generic head on the pinned bsc across all 21 registrations plus one
unregistered; atomic cutover; shuffled-import and old/new .bo mixture
tests. NEEDS-RAVI: ratify gate (a); share the study's companion
artifacts.

## 4. BVI: one construct, four programs (RESOLUTION of the family)

`import "BVI"` appears in four lanes that must stay one design:

- **Decomposition** (artifact-graph §10): an asserted semantic contract
  plus a foreign realization; scheduling annotations become carried
  constraint obligations (asserted, upgradable to validated).
- **Fallback / soft-IP** (bsc-side): a declared pure-Bluespec fallback
  (model or stub tier) selected *structurally* — Verilog binds at
  output time via a per-import ifdef swapping only the module name
  (fallback synthesized through the BVI's own port map), Bluesim binds
  at link, the parent .ba identical in all cases: no new tainting axis.
  RESOLUTION — adopt with Codex's conditions as v1 requirements: an
  explicit binding map + manifest entry (import → real/model/stub,
  tier, trust, source closure, macros, capabilities) rather than
  implicit substitution; schedule refinement compared per permitted
  CALL CONTEXT (same-rule parallel; each cross-rule order — the
  P-into-CF set insertion is not a lattice), sourced from the canonical
  schedule artifact; conformance to the BoundaryBinding/PortTree of §2;
  stubs opt-in and test-gated; effect/trust tier recorded (schedule
  conformance is not behavioral substitutability); same-package v1
  ownership rule with a thin local wrapper; question-mark bodies and
  Bits-only zero stubs are not safe contracts — the stub generator is
  stubOf(IfcContract) at the boundary or a sealed witness with
  roundtrip/definedness laws; VMIfDef integrates explicitly with
  identifier legalization. Status correction (FACT): a two-commit
  old-base implementation exists on origin/verilog-import-fallback;
  the proposal doc is the design of record and the implementation
  rebases onto the schema foundation.
- **trs execution** (BVI-via-Verilator v5, as built): the shadow-vector
  model with an exactness theorem whose refusals are its boundary
  conditions; verilation as a build step; pinned Verilator; oracle
  succession per fixture (iverilog → VCS designated); defined
  divergences pinned, never silent. Its .ba-graft seam (substituting a
  plain-BSV implementation in bsc link-time hierarchy assembly) is the
  same mechanism as the fallback clause seen from the simulator — and
  re-enters the X-freedom proof domain. RESOLUTION: the fallback clause
  and the graft are one design with two consumers; specify once
  (bsc-side), let trs consume the substituted hierarchy.
- **Doctrine** (trs): BVI is last-resort — source-level BSV
  substitution first (keeps the Bluesim oracle), curated prim-table for
  DesignWare-class IP second, verilated-leaf co-sim last. BVI pressure
  at MatX is entirely in the -verilog flow (mkDwSimOrBs picks native
  models under -sim) (FACT).

## 5. Foreign functions: one logical ABI, per-tool transports (RESOLUTION)

Adopt the ForeignABI descriptor: model each foreign function once
(typed args/results, widths, direction, signedness, state domain,
ownership, effect class) with per-transport realizations recorded in
the manifest. The transport matrix of record (FACT): VCS = polymorphic
VPI (no usable polymorphic DPI); released Verilator = width-mangled
monomorphized DPI (IEEE 35.5.4 requires mangled C symbols + generated
shims); the MatX Verilator fork = open-packed DPI (implemented,
validated, UNPUSHED — custody is the chat-delivered patch; re-land
needs a write grant); iverilog = VPI. Monomorphize-with-mangled-symbols
is the portable near-term path; open arrays remain the cleaner form
where supported and an upstream candidate (issue 3198; maintainer has
said "PR welcome" since 2021). NEEDS-RAVI: the upstream plan (R3) and
the MatX-inc/verilator write grant. Note for trs shell: shell exports
have concrete widths at generation time, so mangled DPI serves it on
every tool — the open-packed capability matters for *polymorphic
imports*, not the shell boundary.

## 6. Instance-specific synthesis (issue 921)

The BVI-fallback's parameterized-import tier is the easiest ISS client
(port protocol fully dictated by VModInfo). Staging stands: v1
monomorphic; v1.5 explicit specialization stubs driven by the
frozen-manifest protocol (the InstSynth messageM loop, mechanized);
v2 the ISS engine (GenWrap-during-elaboration at discovered types).
Specialization is driven from the type instantiation during
elaboration — parameter-value inversion at link is unsound (FACT).
Contract-value hashes are the cache keys (T2); demand-driven ba(inst)
rides the artifact graph's reentrant-genModule machinery.

## 7. Retiring genC/genVerilog (RESOLUTION — adopt as a vision item with gates)

Once implementation selection is structural and late-bound, the
elaboration-time backend probes become compatibility relics: parse,
typecheck, elaboration, scheduling, contracts, and symbolic segments
form one backend-neutral cached prefix; only binding-keyed codegen
leaves specialize. Adopt with its two gates: (i) census and migrate
every genC/genVerilog use, representing genuine backend requirements as
explicit capabilities or fail-closed link refusals; (ii) **binding
precedes realization-dependent planning** — implementation selection
must be fixed before PlanB/AOT-layout-class decisions (the live_en/
arena example), i.e. the pipeline is semantic segment → binding +
manifest → conformance + realization plan → link, and a mutable run key
must not retarget an artifact after layout. Prove the payoff with an
implementation-swap test in which the semantic prefix cache-hits.

## 8. Lane pointers

"KB: SplitPorts port-structure design"; "KB: bsc semantic port
properties"; "KB: HuffmanBits generic deriving"; "KB: bsc BVI fallback
+ soft-IP design"; "KB: BVI-via-Verilator design (trs)"; "KB: verilator
open packed DPI"; "KB: bsc typeclass coherence" (orphan enforcement);
"KB: bsc artifact graph" (§§7–10, 13 + reviews); post-genwrap-
compiler.md; bsc issues 921, 1061, 713, 731, 658.

## 9. NEEDS-RAVI (rolled up in 09)

- HuffmanBits adoption gate (a) vs (b); companion artifacts.
- Open-packed DPI upstreaming (R3) + MatX-inc/verilator write grant.
- BVI fallback: ratify the structural binding design with the Codex
  conditions as v1 scope; route the soft-IP implementation rebase.
- SplitPorts: authorize the compile+sweep gate work (a toolchain
  session task).
- Orphan policy: WOrphanInst→error timing (standalone or with P0);
  routing of the GenSign defect filing (own issue vs bsc#1061 comment).
- Port-properties default flip after the capability-visible suite.
