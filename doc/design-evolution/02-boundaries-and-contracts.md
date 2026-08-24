# 02 — Boundaries and Contracts

The semantic/physical split and everything that binds at a boundary:
contracts as values, the port ABI and its witnesses, encodings as ABI,
import "BVI" unified, foreign functions, instance-specific synthesis,
the dissolution of genC/genVerilog, and the SystemVerilog interop ABI.

**Status:** v2.0 — 2026-08-24 (Claude). Design only; sequencing and
status, sequencing, and provenance live in the KB lanes and the
meeting-notes digest, outside this set. Mechanism homes:
RFC-bsc-artifact-graph.md §§7–10, 13; the post-genwrap design; the
SV-interop ABI doctrine note.

## 1. The split

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
with symmetric segment/link seams per backend so any conforming
realization substitutes at link without parent recompilation. Design
for type and schedule/clocking compatibility, never wire
compatibility.

## 2. One owner for the port ABI

Port layout must have a single owner. *Why:* when layout is defined
independently by wrapper generation, the BVI port table, simulator
export paths, top-level lifting, and final identifier legalization,
the failure mode is real hardware corruption with zero diagnostics —
demonstrated by the orphan-mislink study: same-name, same-width ports
with divergent layouts link cleanly (including a reversed-lane pinout
byte-indistinguishable from the correct one), and pinouts can depend
on import order.

RESOLUTION — one canonical **BoundaryBinding/PortTree** owns the
physical ABI: leaf identities and order, final names and the rename
map (candidate names are never authoritative — legalization is part of
the owner), widths, roles, sharing classes, zero-width behavior,
clock/reset ports, and the committed encoding/splitting *evidence*
that produced the layout. Everything else — semantic port properties,
waveform correlation, simulator binding, fallback conformance, editor
touch-points — consumes it. Design invariants:

- **Coherence first**: the classes that select physical
  representation (Bits, SplitPorts, the wrapper classes,
  ValidateBits, literal classes, codebooks) carry a no-orphans
  property, enforced at use sites (04); their instance evidence joins
  artifact identity — typeclass resolution *is* ABI.
- **Structure is kept, not flattened**: a split value keeps the shape
  of its type (a struct splits into one element per field, tuples all
  the way down), and the leaf-order invariant that lets any flat view
  index the tree is checked, not assumed — order, not just count.
- **Schedule-scoped facts are partitioned**: structural role facts may
  live in the semantic contract; rule-liveness, arbitration, and
  enable-folding facts belong to one completed schedule and live in
  the binding, keyed by schedule digest; under dynamic alternatives
  only the intersection across legal arms is contract material.
  Derived boolean facts state their truth domain (two-state vs
  four-state) explicitly.
- One canonical mux/binding plan is shared by lowering and analysis
  (T3): readers never re-derive it.

## 3. Encodings are ABI: the codebook witness

**Width agreement does not imply encoding agreement**; the codebook
policy (merge order, tie-breaking, edge labeling) is ABI. The width
theorem (root height = ceil(log2 Σ 2^p_i)) makes generic deriving of
Huffman-class encodings possible — only the width must be type-level;
tags are elaboration values that partially evaluate away.

RESOLUTION — **one versioned witness per encoding-owning instance**:
pack, decode, and validate are generated from one fingerprinted
codebook witness; the fingerprint joins semantic identity wherever
packed values cross a package, simulator, trace decoder, or cache
boundary; invalid/unknown decode semantics are specified (fail
closed; unpack stays total but never implies validity — ValidateBits
is the validity oracle). Where an encoding is shared with another
language's implementation, equivalence is established by differential
fuzz against that implementation's tables — a roundtrip property is
provably insufficient (it cannot see agreed-but-wrong tables).

## 4. import "BVI": one construct, five programs

The same construct appears in five designs that must stay one:

- **Decomposition**: an asserted semantic contract plus a foreign
  realization; scheduling annotations become carried constraint
  obligations (asserted, upgradable to validated), and the boundary
  is checked when a compiled module is instantiated in a foreign
  design.
- **Fallback / soft-IP**: a declared pure-Bluespec fallback (model or
  stub tier) selected *structurally* — the Verilog realization binds
  at output time by swapping only the module name through the BVI's
  own port map; simulator realizations bind at link; the parent
  artifact is identical in all configurations, so there is no new
  tainting axis. Design conditions: an explicit binding map + manifest
  entry (import → real/model/stub, tier, trust, source closure,
  capabilities) rather than implicit substitution; schedule
  refinement checked per permitted *call context* (same-rule parallel;
  each cross-rule order — set inclusion on relation letters is not the
  check), sourced from the canonical schedule artifact; conformance to
  §2's port owner; stubs opt-in and test-gated, with the stub
  generator derived from the semantic contract or a sealed witness
  with roundtrip/definedness laws — don't-care bodies and
  Bits-only zero stubs are not safe contracts; effect/trust tier
  recorded, because schedule conformance is not behavioral
  substitutability; substitution warnings are emitted by the harness,
  never guarded by configuration macros that legitimate builds define.
- **Foreign execution under a verilated engine**: a shadow-vector
  execution model behind the simulator's primitive ABI, with an
  exactness theorem whose export-time refusals are its boundary
  conditions; verilation is a build step; defined divergences are
  pinned, never silent. Its artifact-graft seam — substituting a
  plain-Bluespec implementation in link-time hierarchy assembly — is
  the fallback clause seen from the simulator, and is what restores
  X-provability (05): specify once, consume twice.
- **Doctrine**: BVI is last-resort — source-level substitution first
  (keeps the reference oracle), a curated primitive table for
  standard-IP classes second, verilated-leaf co-simulation last.
- **The long-horizon rethink**: redo the import surface from scratch
  on top of SplitPorts (the BVI syntax predates the typeclass that now
  owns type↔port mapping), restoring computed module names and
  extending to computed port names — "generally anything with string
  literals." This is the same design as the decomposition bullet
  reached from the surface-syntax side; when built, it is the surface
  for the asserted-contract + foreign-realization split, not a
  parallel construct.

## 5. Foreign functions: one logical ABI, per-tool transports

RESOLUTION — the **ForeignABI descriptor**: model each foreign
function once (typed args/results, widths, direction, signedness,
state domain, ownership, effect class) with per-transport realizations
recorded in the manifest. The transport landscape is a requirement,
not a choice: one major commercial simulator offers no usable
polymorphic DPI (its transport is polymorphic VPI); stock open-source
simulators require width-mangled monomorphized DPI; an open-packed DPI
capability (one import serving all packed widths) exists as a pinned
experimental capability with an upstream path. Monomorphize-with-
mangled-symbols is therefore the portable floor; open arrays remain
the cleaner form where supported. "DPI yes/no" is not a manifest
entry — transport identity, link identity, and collision checks are.
Simulator-shell exports are expected to be monomorphic at generation
time (widths concrete), making mangled DPI sufficient there — a
reading to be confirmed (08); if a width-polymorphic shell boundary
ever exists, the VPI realization covers it.

## 6. Instance-specific synthesis

Polymorphic imports and parameterized IP want per-instance synthesis:
specialization is driven from the type instantiation during
elaboration — parameter-value inversion at link is unsound (FACT).
Staging by design: monomorphic first; explicit specialization stubs
driven by a frozen-manifest protocol; then the full engine
(wrapper-generation during elaboration at discovered types).
Contract-value hashes are the cache keys (T2); demand-driven
per-instance artifacts ride the graph's reentrant elaboration
machinery.

## 7. Dissolving genC/genVerilog

Once implementation selection is structural and late-bound, the
elaboration-time backend probes become compatibility relics: parse,
typecheck, elaboration, scheduling, contracts, and symbolic segments
form one backend-neutral cached prefix; only binding-keyed codegen
leaves specialize. The stated end state: backend-agnostic
implementation artifacts with selection at link — "elaborate once,
simulate many ways"; encrypted-IP swaps, test stubbing, and
behavioral memories become link choices. Standing customer classes
for per-instance selection: encrypted-IP substitutes,
computed-parameter imports, conditional emulation-with-coverage
builds, X-mode simulation profiles, and behavioral fallbacks for
foreign modules without a native model. Two design rules make it
sound: (i) genuine backend requirements are represented as explicit
capabilities or fail-closed link refusals, never probes; (ii)
**binding precedes realization-dependent planning** — implementation
selection is fixed before layout-class decisions, and a mutable run
key must never retarget an artifact after layout. This retirement
depends on schedule specification (03): a checked schedule contract is
what makes multiple implementations of one boundary safe.

## 8. The SystemVerilog interop ABI

The rendering of Bluespec types into SystemVerilog and Rust — packed
layouts, field/tag names, tag encodings including variable-length
codes, canonical form, package structure — is governed as **one ABI**
(the doctrine note; ratified as policy):

- **Canonical form is clause 1**: what equality masks and what
  generation fills for don't-care bits.
- **The one-library rule**: every language emitter is a projection of
  ONE type-to-rendering library — two hand-maintained descriptions are
  two ABIs, and name drift between them has already shipped a bug
  class once.
- A written compatibility policy per type-edit class; versioned type
  names for freezes (freeze one name, not N bit indices); a golden
  layout manifest as a CI check.
- **Ship-in-pairs bidirectionality**: pack/unpack (for encoded types
  the codec IS the boundary; prefix matchers are emitted logic, never
  solver problems); render/project (typed port emission pairs with
  typed views); name/select (accessor packages over bit-index
  selection). The read side is pure selection; mutation stays
  Bluespec-side; dynamic projection out of encoded types is real
  hardware cost and opt-in.
- The accepted cost is compiler layout freedom: layout changes become
  ABI events.

The broader SV output horizon rides the same machinery: SV-type
integration generated from the same witness as §3 (never a parallel
implementation); intent-bearing constructs — always_ff/always_comb/
logic and especially **unique case**, which propagates the compiler's
exhaustive-and-exclusive-by-construction knowledge to downstream tools
that would otherwise reprove or miss it (T1 applied to the backend);
SV assertion emission; native SV import as the richer sibling of §4's
import rethink.

## 9. Pointers

Mechanism and evidence: the artifact-graph RFC's contract sections;
the post-genwrap design; the SplitPorts, semantic-port-properties,
HuffmanBits, BVI-fallback, BVI-via-Verilator, and open-packed-DPI
lanes; the SV-interop ABI doctrine note; the orphan-mislink study.
Indexed in the KB; open design decisions in 08.

## 10. RESOLUTIONS and OPEN questions

- RESOLUTION: one port-ABI owner; coherence enforcement precedes any
  serialized physical-ABI change; leaf order checked by construction
  AND validated.
- RESOLUTION: one versioned codebook witness; differential fuzz
  against the sibling implementation is the equivalence gate.
- RESOLUTION: the fallback clause and the simulator graft are one
  design with two consumers.
- RESOLUTION: the ForeignABI descriptor with per-tool realizations;
  the interop ABI's one-library rule.
- OPEN: the codebook adoption gate — port the existing planner exactly
  vs canonicalize both sides (a pre-silicon flag-day choice).
- OPEN: strict conformance mode as default for foreign execution.
- OPEN: canonical-form clause ratification; anonymous/structural
  types at boundaries; recursive encoded types (the doctrine's queue).
