# 07 — Use Models: Requirements and Their Conflicts

The design of 00–06 serves two use models. This document states each
as a set of requirements, shows how requirements drive design
responses, and names where the two models' requirements genuinely
conflict — with the design posture that resolves or contains each
conflict. Deployment history, schedules, and organization are not
design and live in the KB record; the open design questions are in 08.

**Status:** v2.0 — 2026-08-24 (Claude). The governing thesis is T9: a
fork, a pin, or a mode is a binding choice recorded in a manifest,
never an unrecorded divergence.

## 1. The external use model (requirements)

An open ecosystem of independent users and contributors. The design
must serve:

- Distro-installable toolchains; no new mandatory installs (solvers
  bundled and pinned, never PATH-discovered).
- Stable CLI surfaces and test-authoring conventions: test authors
  never write Haskell; the existing test-driver workflow survives any
  orchestration change.
- Four-state, event-driven simulators as the semantic frame of
  reference; hand-written Verilog integration; stable pinouts for
  integrators.
- Backward compatibility as a default: semantic breaks are priced by
  census, named, versioned, and shipped with legacy modes.
- Literature-grounded, GHC-compatible language surfaces.
- Bluesim ships and stays: for many users it is the only simulator;
  its kernel ABI is public surface.
- Review capacity is scarce: changes arrive upstream-shaped, small,
  evidence-carrying, and independently landable.

## 2. The MatX-style use model (requirements)

A single organization building large chips from Bluespec with heavy
code generation and an agent-assisted workflow. Things we want for our
use model, stated as requirements on the design:

- **Static, hermetic builds with remote caching.** The compiler's
  artifact graph must be containable by a Bazel-class build system:
  declared inputs, tree artifacts, persistent workers, a
  remote-execution-backed cache, frozen specialization manifests
  (01 §1). Compile cost is first-order economics — Bluespec
  compilation alone has been measured at ~half the critical path of
  an integration pipeline — so caching correctness and compile-time
  scaling are requirements, not conveniences.
- **Byte-stable artifacts as release currency.** Generated Verilog is
  diffed byte-for-byte to detect codegen change; determinism by
  construction or by seal (01 §6). Port and module names are
  downstream ABI (physical design, DV goldens, netlist tooling), so
  the port owner and rename map of 02 §2 are requirements here, not
  elegance.
- **Commercial-simulator and encrypted-IP support.** VCS-class tools
  must be drivable (polymorphic VPI where DPI is unavailable — 02 §5);
  encrypted IP must bind at link as a realization choice (02 §7); a
  simulator shell must slot into existing generated-Verilog flows
  (05 §1.7).
- **Generated types at scale.** Wide, machine-generated interface
  types (vectors of interfaces, deep structs) make wrapper-generation
  economics, split-port structure, and typechecker scaling
  requirements (02 §2, 04 §§3,5); type definitions are shared with a
  Rust implementation, making cross-language layout an ABI (02 §§3,8).
- **Usage style.** The Haskell-syntax front end almost exclusively;
  rules constructed by module-monad functions rather than explicit
  rule blocks; implicit conditions off; a scheduler-inserted stall is
  a bug, not conflict resolution. The design must keep this style
  first-class: stated intent over inferred permissiveness (T6).
- **Workload shape.** Measured: replicated wire-heavy fabrics whose
  simulation cost is runtime-bounce-bound, versus external
  processor-class cores that are codegen/memory-bound (~96% of
  instructions in the compiled artifact vs ~4%). One simulator, two
  economies — so lever verdicts are corpus-conditional by design and
  performance claims stay shape-specific (05 §1).
- **Agent-driven development.** LLM agents are first-class consumers
  of the LSP, the query surface, and observability (06): machine-
  legible diagnostics, action-keyed authority, probe tools over
  viewers.
- **Two-state speed with X soundness on demand.** Fast two-state
  simulation for parity and benchmarking, with X-fidelity delivered
  by proof (certificates) rather than by pervasive four-state cost
  (05 §2).

## 3. Requirements → design responses

| Requirement pressure | Design response |
|---|---|
| External: 4-state frame of reference. MatX: 2-state speed + proofs | X in trs only; 3-state reference + 2-state benchmarking mode; X policy vector in manifests; certificates scope claims; verilated islands declared (05 §2) |
| External: stock simulators, fixes upstreamed. MatX: trusted pinned engines | Pins are bridges with upstream exit plans; capability-probed, bundled engines behind stable seams; pin identity in manifests (05 §4) |
| External: VPI where required. MatX: one clean FFI transport | ForeignABI descriptor: one logical function, per-tool transport realizations in artifact identity (02 §5) |
| External: schedule compatibility. MatX: named schedules, dynamic selection | One order with priced, versioned migration; positions/footprints as contracts; pinned arm tables (03) |
| External: `bsc -u` convenience. MatX: static hermetic containment | One graph, two orchestrations: the engine serves interactive dynamic builds and is containable by frozen manifests (01 §1) |
| External: test authors keep their workflow. MatX: fleet-scale verdict caching | Verdict nodes with earned cacheability classes; orchestration-neutral checkers; migration only when the engine premise holds (01 §5) |
| External: distro toolchains. MatX: deterministic ccache-able fleet builds | Determinism as designed property; total tie-breaks; build-twice invariants (01 §6) |
| External: Bluesim ships. MatX: trs performance | Frozen-bsc side-tree; flavor transparency; engine-agnostic boundaries; replacement by proof (05 §1) |
| External: derived-encoding stability. MatX: encodings shared with Rust | Codebook witness, fingerprint in identity; one type-to-rendering library; interop ABI clauses (02 §§3,8) |
| External: stable pinouts. MatX: generated types, name-keyed downstream ABI | One BoundaryBinding/PortTree owner; leaf order checked; rename map owned (02 §2) |
| External: literature-grounded extensions. MatX: generated-code ergonomics now | Extensions designed upstream-shaped; use-model previews are bindings, not forks (T9) |
| External: no install burden. MatX: solver-heavy proof flows | Solvers bundled and pinned in the tool tree; heavy proof stacks ship with trs, not core bsc (04 §4) |
| External: an LSP at all. MatX: agent-grade tooling now | Two-layer LSP, upstream-shaped; agents as a named consumer class; action-keyed authority (06 §2) |

## 4. Requirement conflicts resolved by design

- **Fork pressure vs upstream convergence.** The frozen-bsc side-tree,
  alive-but-empty tool forks, preview bindings, and
  orphan-improvements-as-small-changes all implement one rule: keep
  the fork surface enumerable, keep every divergence upstreamable or
  manifest-recorded, and let caches key on the binding.
- **Byte-exactness discipline vs evolution.** Change is either
  invisible (transposes, caches, metadata — proven byte-identical) or
  a versioned event (one order, format generations, the reset and
  finish contracts). This is what lets aggressive restructuring
  coexist with an ecosystem.
- **One engine's semantics vs many engines' quirks.** The oracle
  lattice with pinned divergence classes replaces "match Verilog"
  (ill-posed) with per-contract, per-oracle witnesses (05 §4); the
  hardware-model line keeps simulator emulation out of library
  semantics (00 §2).
- **Style divergence vs one language.** Implicit-conditions-off and
  constructed rules are configuration and library surface, not
  dialect: the same semantics, different defaults — and the one-order
  model is priced by exactly the divergence census that protects
  users of the other defaults (03 §1).

## 5. Requirement conflicts NOT resolved by design (strategy — 08 §C)

1. **Where trs ultimately lives**: side-tree product forever, or an
   eventual upstream offering (tool suite vs backend). This decides
   whether BIR versioning is an internal or public contract, and
   whether "Bluesim remains" has an expiry for external users.
2. **The one-order break's ecosystem posture**: the census will
   price it; whether the model is ever part of the shared language is
   a judgment call after the numbers.
3. **Commercial-simulator engineering depth**: encrypted IP is the
   one hard VCS requirement; how much design investment the
   VCS-specific paths deserve is a priority call, not a design fact.
4. The design assumes an upstream that reviews — evidence-carrying
   changes that can land; sustaining that is process, not
   architecture, and lives outside this set.

## 6. Pointers

The use-model requirements trace to: the trs full-AOT lane (workload
shape, lever verdicts), the artifact-graph RFC (containment), the
issue inventory (the external footprint), the interop-ABI doctrine
and codebook study (shared encodings), the LSP lane (agents as
consumers), and the monorepo ground-truth survey. Deployment history
and the meeting-sourced record: the KB meeting-notes digest. The
open questions: 08.
