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
shape-specific. The MatX-side campaign numbers of record (FACT, moved
here from 05 per the doc-set rule): 136 corpus tests byte-exact
all-AOT with zero known parity divergences; wire-heavy benches 2.4–6.6×
faster than Bluesim -O3; unit tests ~10× end-to-end (boot 4–6ms vs
bluetcl 55–70ms).

The usage-style divergence is equally structural (FACT, compiler tour):
MatX writes the Haskell-syntax (classic/BH) front end almost
exclusively; rules are mostly *constructed* by module-monad functions
built on the prelude's rule-manipulation primitives rather than written
as explicit rules-blocks; implicit conditions are turned off; and a
scheduler-inserted stall is treated as a bug, not as conflict
resolution — several stock defaults are flipped accordingly. The
bootcamp pedagogy teaches the same posture (explicit design style over
implicit conditions; debug from source analysis, never from generated
Verilog). Upstream's defaults serve the opposite audience. Any change
to default scheduling/implicit-condition behavior therefore prices out
differently in the two worlds — one more reason the one-order break
gets a census and a compatibility rung (03).

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
   the MatX bsc repo; upstream's "bsc as smaller tools" direction —
   whose origin is now on the record (the 2026-08-21 sync adopted the
   3-phase compile split and contract files; 10 §1) — suggests an
   eventual upstream-adjacent home. Whether trs is ever offered
   upstream, and in what form (tool suite vs backend), is a strategy
   call no lane records.
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

## 5. The meeting record on the MatX side (2026 crawl)

MatX-specific material from the meeting-notes crawl (10 records the
Bluespec-general half). All items FACT unless labeled.

**Release engineering of the fork.** Releases are cut from main
(main = the release branch; 2026.4.2 was release-branch + 2 PRs), with
benchmarking and output verification mandated for every release (5-run
averaging; scripts provided). The consumption architecture settled in
August: **three concurrent compiler release channels — production,
preview, local-build** — with cherry-picking onto release branches to
stay current despite upstream review latency, stacked PRs to decompose
large branches, and **manifest-based branching** with a materialized
preview branch as the testing baseline (a manifest tool exists and is
being improved). DECISION (Aug 13): non-upstreamed features are managed
via external scripts, never core-compiler modifications; the
non-upstreamed lines of work in each release get documented. A compiler
freeze for tape-out is planned. This is T2/T9 arriving through
practice: the release manifests are the productized ancestor of 01's
transitive-manifest program.

**Hardware arcs the compiler serves.**
- *CSRs*: the RDL flow generates **typed Bluespec and SystemVerilog
  from a Rust type field in the register definition** (RDL files are
  the source of truth; typed interfaces, not raw bits; backdoor
  interfaces eliminated); block architecture consensus is APB clients
  off controller blocks rather than direct CSR clients; Bluespec's
  type safety and metaprogramming are the cited advantage for CSR
  datapaths; the sim model must match RTL with the same host software
  on both.
- *Interface decomposition* (May 7, the port-splitting origin):
  monolithic interface methods cause scheduling circularity; decompose
  into independently scheduled actions with bypass wires; Rust
  interface generation limited to top-level subsystems.
- *Verification framing* (Mar 25): the traditional method — a Haskell
  model plus the Bluespec representation extracting stimulus and
  expected responses — against brittle independent DV tests; the TA and
  RE DMA engines are internally different (descriptor-table encodings),
  falsifying the "uber DMA descriptor type" modeling assumption.
- *Validation in production* (Aug 20): DMA-descriptor architectural
  validation uses unknown-checks that preserve synthesis structures —
  ValidateBits/primIsUnknown in real use on MatX RTL. ValidateBits is
  also the recorded internal feature ask from the A0-freeze review
  (Erez 1:1; Lucas's bit-pattern validity checking).
- *Coverage*: a Bluespec **coverage story** (coverage-tracking
  infrastructure) is committed in the project portfolio, with a
  coverage document shared internally; the document itself was not
  reachable by this crawl (10 §7).
- *Simulation targets*: Verilator adoption targeted at 90% for local
  testing flexibility; the Rust simulator gets benchmarked on the
  RISC-V SoC; simulator-comparison benchmarking moves to **public
  open-source suites so results can be shared without exposing IP**
  (consistent with the trs campaign's public-corpus posture);
  simulation decouples from synthesis so non-synthesizable debug
  features stay available. Bluesim remains one of the few simulation
  paths that works on Mac — the reason the ramp menu keeps the
  Bluesim-C++-to-build-system handoff alive even though MatX uses
  Bluesim less than typical Bluespec shops. Ground-truth check
  (repo survey): **trs has zero references in the monorepo today** —
  "MatX-internal" currently means the fork plus the trs PR stack, and
  fleet adoption (replacing the BscBluesimLink/-O1 path with trs link
  under the byte-stability release bar) is a separate, post-freeze,
  currently *unowned* rollout design. A standing caution from the same
  survey: the one fork scheduling-default flip that reached the fleet
  (-no-aggressive-conditions) produced a quadratic interaction
  (upstream #1056) the monorepo still works around on every build —
  fork-default scheduling changes leak.
- *Lint policy* (Jul 23): DECISION — implement compiler patches
  directly with no toggle flags (deadline pressure); two-tier strategy
  (reduce lint noise in generated Verilog; better warnings for real
  issues); simulation-only signals categorized away from hardware
  logic (probes under translate_off); "identifying real bugs before PD
  remains critical."
- *b2v pipeline*: r2 translates Rust ISA types to Bluespec (types must
  be *unpacked* because Bluespec lacks type families — a concrete MatX
  motivation for the ATF program in 04); b2v translates onward to SV
  via Generic for DV consumers. Ramp-menu items: emit == and ===
  alongside b2v types and generate *validation* functions, tested
  differentially against the Rust Bits trait (which validates —
  "Bluespec doesn't, in the pursuit of more efficient hardware") and
  against ValidateBits once landed. BVI pressure at MatX concentrates
  entirely in the -verilog flow (mkDwSimOrBs picks native models under
  -sim); the trs BVI census residue on the corpus is five permanent
  Inout cases plus the one mesa leaf (02 §4, 05 §3).
- *PD quality loop* (Chris's arc, Aug 10–17): Yosys-based rapid
  pre-synthesis floor-plan analysis (Manhattan-distance × flop-count
  tension metric; DEF/LEF parsing at scale; grid heat maps; a combined
  memory bank as the validation case), plus bluetcl+JSON bus-type
  extraction for the PD team — the concrete descendant of the Mar 20
  "fast hardware-quality feedback loop" requirement.

**Organizational context that bounds the design work.** Compiler-team
scope formally expanded beyond the single compiler (tools &
infrastructure); the schedule shifts off A0 on Oct 1 toward the next
tape-out, consistent with §1's freeze horizon. An org-level **repo
separation mandate** (monorepo → separate repositories) landed in
August with concerns recorded (integration, discoverability, atomic
commits) and productivity measurement as mitigation — it intersects P1
(build/driver work) and strengthens the manifest program, since
cross-repo composition without atomic commits leans harder on artifact
identity ("intelligent build systems remain necessary" under either
structure). Hiring: two compiler-team hires approved; the strategy of
record since March is "hire competent Haskell programmers, teach them
hardware with LLM assistance"; interviews use collaborative RTL
exercises; verification hiring prioritizes type-based thinking
(Rust/OCaml/Haskell). The internal teaching curriculum (RTL→BS concept
sequence ending at "bluespec patterns") is the onboarding complement.

## 6. Lane pointers

Every lane contributes here; the concentrated sources are "KB: trs
full-AOT push" (doctrine + corpus inversion), "KB: bsc artifact graph"
(S0–S4 staircase, Bazel containment, premise routing), "KB:
BVI-via-Verilator design" (pin posture, oracle succession), "KB: bsc
issue inventory" (the upstream footprint: 96 issues, workaround
cross-references), "KB: HW repo short-term strategy" (freeze horizon,
governance), "KB: Bluespec LSP design" (engagement), the matx repo's
third_party/bluespec pinning machinery, and — for §5 — the meeting
corpus indexed in 10.

## 7. NEEDS-RAVI

Items 1–5 of §4, plus: the issue-inventory identity questions (sec E)
and Codex's design-ownership-map proposal (issue → owning design → PR
stack → gate), which this document set partially implements and 08/09
complete.
