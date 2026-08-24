# 07 — Two Worlds: Upstream Bluespec and MatX

Where the external/upstream use case and the MatX use case pull the
design in different directions, and the posture that resolves each.

**Status:** v1.0 — 2026-08-24 (Claude, holistic review). The governing
thesis is T9: a fork, a pin, or a mode is a binding choice recorded in
a manifest, never an unrecorded divergence. Labels as elsewhere.

## 1. The structural difference

Upstream bsc serves an open ecosystem: dynamic Shake-native builds,
DejaGNU-invoked tests, distro toolchains, four-state event-driven
simulators, hand-written Verilog integration, contributors who write
Tcl test scripts and expect stable CLI surfaces. MatX serves one
monorepo: static Bazel graphs with remote execution, pinned toolchains
delivered as release archives (bazel/config/http.MODULE.bazel;
bsc-preview channels; MATX_BSC_LOCAL), generated code (r2/IsaR2*, b2v),
lint gates (//rtl:BsLint), Verilog-flavored .ba as the default flavor,
VCS licenses, and a schedule (A0 freeze 2026-10-01; PN99.1; bsc freeze
ending ~Jan 2027 when B0 RTL begins; compiler perf changes gated by a
Mieszko/Charlie risk review).

The deepest *measured* divergence is workload shape: Flute/Toooba-class
external cores are codegen/memory-bound (95.7% of instructions in the
compiled artifact; I-footprint and D1 locality dominate) while MatX RTL
shapes were runtime-bounce-bound (artifact ~4%; wires/trampolines
dominated) — one simulator, two economies. Lever verdicts are therefore
corpus-conditional by design, and performance claims stay
shape-specific.

## 2. The per-axis postures

| Axis | External pull | MatX pull | Posture (RESOLUTION unless marked) |
|---|---|---|---|
| X semantics | 4-state Verilog world; event-driven oracles | 2-state speed; byte parity; proofs | DECISION: trs 3-state reference + 2-state benchmarking mode; X only in trs; Bluesim = designated world + sampler; X policy vector in manifests; BVI islands scoped |
| Verilator | converge to stock upstream; file fixes as PRs | pinned fork release (material miscompile fixed; open-packed DPI) | Pin now, upstream both fixes, fork stays alive-but-empty as emergency vehicle; open-packed DPI upstream decision = R3 (NEEDS-RAVI) |
| FFI transport | VPI everywhere it must; DPI where standard | one polymorphic import (open-packed) on the pinned fork | ForeignABI descriptor with per-tool realizations in manifests; monomorphized DPI as portable floor; VCS stays polymorphic VPI |
| Scheduling model | backward compatibility; attribute surface | one order; positions; trs dynamic scheduling | DECISION one order + the compatibility rung (census, format generations, legacy mode); pragma surface demotes to constructors with unchanged spellings |
| Build | Shake-native dynamic graph; `bsc -u` users get parallelism free | Bazel containment (tree artifacts, workers, REAPI share, frozen manifests) | One graph, two orchestrations; frozen/manifest mode is the bridge hook designed in from day one |
| Testsuite | DejaGNU-invoked; test authors write Tcl; freeze through the build switch | matrix growth; differential populations; fleet verdict caching | Migrate only under the upstream-landed premise; "test authors never write Haskell" is a hard requirement; fork-only = do not migrate the corpus |
| Compiler identity | GHC toolchains from ghcup; distro packagers | deterministic ccache-able builds at fleet scale | findBest patch upstream to GHC; Warmup + sane -j defaults upstream to bsc; one-shot mode where by-construction determinism is wanted |
| Simulator | Bluesim ships; Verilog backend is the product | trs replaces Bluesim *when proven*; trs shell into VCS flows | Frozen-bsc side-tree keeps the fork surface ~zero; flavor transparency + dual-flavor seal keep one BIR semantics; certificates gate replacement |
| Encodings | derived Bits stability | Huffman codebooks shared with Rust (r2/bits crate) | Codebook witness + fingerprint in identity; gate (a) exact assign_tags port (NEEDS-RAVI) |
| Port ABI | stable pinouts for integrators; #713 boundary structure | SplitPorts deriving via ShallowSplit; generated types; DFT/ECO keying on names | One BoundaryBinding/PortTree owner; orphan enforcement first; leaf-order by construction AND checked |
| Language extensions | literature-grounded, GHC-compatible surfaces (VTA, deriving-via, pattern checking) | unblock generated-code ergonomics now (preview channels) | Extensions designed upstream-shaped; MatX previews via bsc-preview repos; policy DECISION 2026-08-15 stands |
| Solvers | no new install burden; distro-friendly | bundled pinned engines; VCS-adjacent flows | Bundle in inst/lib/solvers on the pin rails; never PATH; typechecker stays native (conversational-algebra exclusion) |
| LSP / tooling | upstream wants an LSP; portable editors | daily-driver now; VS Code heavy; Unison funding | Two-layer LSP upstream-shaped; PR 891 bridges; upstream-review program prevents de facto takeover |
| Process | PR-policy hold; staged persuasion (S0–S4); censuses before proposals | per-rung PRs; sealed evidence; landing practice | Every ecosystem-facing change ships with its census and its compatibility rung; the PR hold is Ravi's gate |

## 3. The tensions that resolve by architecture

- **Fork pressure vs upstream convergence.** The frozen-bsc side-tree
  (trs), the alive-but-empty Verilator fork, preview channels, and
  orphan-improvements-as-tiny-PRs all implement the same rule: keep the
  fork surface enumerable, keep every divergence either upstreamable or
  manifest-recorded, and let caches key on the binding.
- **Byte-exactness discipline vs evolution.** The corpus's central
  method — byte-identical transformations, golden churn taxonomized,
  flag-days named — is what lets aggressive restructuring coexist with
  an ecosystem: change is either invisible (transposes, caches,
  metadata) or a versioned event (one order, format generations, reset
  sequence, $finish ordering).
- **One engine's semantics vs many engines' quirks.** The oracle
  lattice (Bluesim ↔ trs ↔ iverilog ↔ Verilator ↔ VCS) plus pinned
  divergence classes replaces "match Verilog" (ill-posed — the LRM
  disagrees with itself across a rewrite) with per-contract, per-oracle
  witnesses.

## 4. The tensions that do NOT resolve by architecture (NEEDS-RAVI)

1. **Where trs ultimately lives.** The side-tree doctrine keeps trs in
   the MatX bsc repo; upstream's "bsc as smaller tools" direction (the
   sync philosophy whose notes never reached the KB — a recorded gap
   worth backfilling) suggests an eventual upstream-adjacent home.
   Whether trs is ever offered upstream, and in what form (tool suite
   vs backend), is a strategy call no lane records.
2. **The one-order break's ecosystem cost.** The census will price it,
   but accepting the break for upstream users (vs fork-first) is a
   judgment call after the numbers.
3. **VCS's role.** Designated test-time oracle (decided) — but the
   trs-shell-under-VCS product and the encrypted-IP story tie MatX to
   VCS in ways upstream users won't share; how much engineering the
   VCS-specific paths get is a priority call.
4. **Upstream review bandwidth.** The coherence stack has been idle
   since July awaiting review; PRs #108–#158 carry zero review
   comments; the Bluespec, Inc. program (~$225K) exists to fix exactly
   this. Funding and sequencing are Monday-meeting decisions, not
   design.
5. **The compat features' route** ('0/'1 classic literals,
   deriving-via): stack rung vs upstream PRs first.

## 5. Lane pointers

Every lane contributes here; the concentrated sources are "KB: trs
full-AOT push" (doctrine + corpus inversion), "KB: bsc artifact graph"
(S0–S4 staircase, Bazel containment, premise routing), "KB:
BVI-via-Verilator design" (pin posture, oracle succession), "KB: bsc
issue inventory" (the upstream footprint: 96 issues, workaround
cross-references), "KB: HW repo short-term strategy" (freeze horizon,
governance), "KB: Bluespec LSP design" (engagement), and the matx
repo's third_party/bluespec pinning machinery.

## 6. NEEDS-RAVI

Items 1–5 of §4, plus: the issue-inventory identity questions (sec E)
and Codex's design-ownership-map proposal (issue → owning design → PR
stack → gate), which this document set partially implements and 08/09
complete.
