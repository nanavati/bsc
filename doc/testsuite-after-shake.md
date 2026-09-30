# The Testsuite After Shake: Pros and Cons

Should the testsuite follow the compiler onto Shake — the full weighing.

**Status:** Analysis v1.3 — 2026-08-23; measured economics folded in
2026-09-29; sequencing revised to engine-first 2026-09-30; adversarial
review round folded in 2026-09-30 (Ravi Nanavati with Claude).
Written as the decision-support expansion of
`RFC-bsc-artifact-graph.md` §16, which answers this question in
compressed, normative form (yes — conditional, sequenced, gated). This
document weighs both sides at full strength: the pros with their
scope conditions attached, the cons at their strongest, the null
hypothesis priced separately, the precedents on both poles, and the
conditions under which the verdict flips. On any divergence, the
RFC's current revision governs; this document argues, the RFC
records. Not proposed upstream.
v1.1 replaces the order-of-magnitude judgments with measured numbers
(2026-09-29 session; full provenance in the KB record "bsc testsuite
CI economics (measured)"): the cost baseline in §2, the enlarged null
hypothesis in §3 (the invocation-cache wrapper is orchestrator-neutral),
the measured asymmetry and cache economics in §6, the census first-cut
in §7(b), and the revised now-list in §8. Two standing constraints
adopted from that session: **run everything, always** (no path-based
test scoping, no AI-scoped selection — pruning happens only by content
identity, and the periodic uncached sweep is cache *verification*, not
scoping), and verdicts key on the *input* closure (sim-output
nondeterminism downstream of a trusted `.ba` is harmless).
v1.2 (2026-09-30) revises the sequencing, not the analysis: given the
settled direction that bsc's own orchestration moves to Shake or an
equivalent (RFC §3/§11), the engine — scoped as the `-u` replacement
with a persistent, invocation-wide cache — is built first and proven
on bsc's own build, and the §3 wrapper is reclassified from
recommended first move to **contingency**. The identity layer (`.ba`
content digest, the input manifest, flag partitioning) is unchanged
in content but moves from wrapper infrastructure to the engine's
first milestone. Three engine requirements surfaced by testsuite
analysis are recorded here (§3, §8) and normatively in RFC v0.23 §3:
byte-identical diagnostic replay on cache hits, cache probes under
every compile entry point (not only the `-u` driver), and coverage
through the link stages. The harness-side verdict layer (verdict-skip,
sim-run skip) is permanent in every ordering; only the wrapper's
interposition shim was ever disposable.
v1.3 (2026-09-30) folds in the adversarial review round (ChatGPT; KB
draft "REVIEW REQUEST — bsc engine-first proposal (adversarial)") and
the delivery planning it produced. Two review blockers become
requirements: a **recursive cache-bypass channel** (non-cacheability
must propagate downward — a performance or staleness test that re-runs
while its inner bsc invocation hits the cache measures a lookup, not
the compiler; "zero harness change" is corrected to "zero `.exp` edits
plus a bypass channel for the never-memoize populations", and uncached
audits must bypass every cache layer), and **`.ba`
digest-vs-loadability** (a content digest changes equality, not the
loader's hard version check — cross-build `.ba` reuse needs an
envelope/payload rematerialization policy or a repriced conservative
cross-version miss). Also adopted: the engine gives artifact-grain
dedup and cutoff to the *un-migrated* harness, so P1–P2's
"impossible from outside" softens to "impossible without the engine";
economics labeled modeled-vs-measured with the audit cadence priced
rather than asserted; the fingerprint unit fixed as three producer
components in private cabal sublibraries (.bo/.ba, .v, .cxx/.h over
supporting components; Ravi); the baseline pinned to the **B0
manifest** (bsc.cabal + cabal.project on release-devel-B0 —
cabalization with thin executables already landed); and the delivery
vehicle recorded (ChatGPT's "bsc orchestration and rebuild
implementation plan", Revision 2, with this round's corrections:
the library build is `.bo`-only so the `.ba` migration gates backend
reuse, not the library win; the legacy port-properties option is
`-semantic-ports-comment`, comment-only).

---

## 1. The question, and what the premise means

The question is **not** "should the testsuite leave DejaGNU?" Asked
cold, that was answered on 2026-08-23 (morning analysis): no — do not
migrate; freeze through the build switch; harvest checker wins in
place. The right question (Ravi's reframe): **after bsc itself
switches to Shake, should the testsuite follow?**

"After bsc switches" has a precise meaning — the §3 ladder's rung 2
has landed: `bsc -u` *is* the Shake engine, shake is in the
compiler's own dependencies, and the custom staleness walker is
deleted. The premise has two readings, and they price differently:

- **Upstream-landed**: B-Lang-org has accepted the engine. The
  follow-on is then argued to maintainers who already run Shake
  inside bsc, and DejaGNU + make + perl is the last redundant
  orchestrator in the repository.
- **Fork-only**: the engine lives only in the MatX/nanavati lineage.
  Every `.exp` diff from upstream becomes a permanent translation
  tax, and the morning recommendation stands unchanged: do not
  migrate the corpus ahead of upstream.

Everything below assumes the upstream reading unless stated. Under
fork-only, skip to §7: the verdict flips.

## 2. Baseline: what the testsuite is today

Measured in-session (2026-08-23), the facts a decision rests on:

- **Corpus**: 880 test `.exp` files, 26,368 lines, ~757 control-flow
  constructs (the rest is straight-line proc calls); 2,983 golden
  `.expected` files; 948 per-directory Makefiles of trivial clean
  plumbing. ~48k checks in the fullest configuration (48,130 PASS /
  264 XFAIL, fullparallel-iverilog); ~19–20k in default configs.
- **Harness**: `config/unix.exp`, 4,063 lines / 228 procs;
  `config/verilog.tcl`, 20 procs dispatching 7 Verilog simulators.
  DejaGNU is used as a **batch driver only** — zero expect/spawn
  usage anywhere in the suite.
- **Execution layer**: parallelism, load balance (timing.txt
  feedback), TESTDIRS CI sharding, and `.sum` aggregation are the
  repo's **own make+perl machinery**, which exists precisely because
  DejaGNU has no execution semantics.
- **Trajectory**: the matrix grows multiplicatively (backends ×
  simulators × combined/separate modes × BVI import paths × engines)
  and its newest assertions are **differential** (cell vs cell).
  diffsweep — the first differential population — already lives
  outside DejaGNU: the matrix has begun outgrowing the harness on
  its own.
- **Cost** (measured 2026-09-29, from the harness's own per-command
  timing in live CI): a full Ubuntu sweep is **17,328 CPU+SYS
  seconds ≈ 4.8 core-hours** — verilator leg 9,547 s (55% of it the
  verilator C++ builds of generated `.v`, even with ccache), main leg
  7,780 s (codegen compiles 36%, Bluesim gen+link 34%; the measured
  36-minute wall). The suite is CPU-bound (wall/(cpu+sys) ≤ 1.04 on
  every heavy category), simulator *runs* are <5% of the work, and
  the committed timing snapshot is ~6× stale against a current run.
  One measured surprise: CI's ccache is **cross-run cold** at main's
  push cadence (every observed "hit" is within-run duplication;
  GitHub's cache eviction outpaces the weeks between main pushes) —
  so these costs are effectively *uncached today*, and every caching
  win priced below is additive to reality, not to a warm baseline.

## 3. The null hypothesis: what we get without migrating

The morning synthesis decomposed the opportunity into three lanes,
and only one of them requires migration:

- **Checker intelligence is orchestrator-neutral.** The S1 tools —
  the timestamped-multiset comparator, the Verilog alpha-equivalence
  checker, the structured per-check verdict emitter with stable check
  IDs — are standalone compiled tools that deploy under DejaGNU today
  and carry over unchanged. They capture the correctness-quality wins
  (order-insensitive comparison, naming-drift-immune Verilog
  comparison, machine-readable results) with zero migration risk.
- **ccache works now** (bsc takes the C++ compiler from `CXX`; the
  harness deliberately re-enables it) — but measurement demoted this
  lane: on CI it is structurally cold across runs at main's push
  cadence, and even warm it cannot touch the two dominant buckets
  (the verilate step and links are outside ccache; `.v`-keyed build
  caching is needed to skip them).
- **The invocation-cache wrapper** (measured design, 2026-09-29;
  since v1.2 the *contingency*, not the first move — §8) is the null
  hypothesis's biggest addition: a content-addressed cache
  behind the `$BSC`/`$BLUETCL`/PATH seams the harness already uses —
  keys = source + imported-`.bo` closure + flags + per-component
  compiler-source hashes; replay = outputs *plus byte-exact
  stdout/stderr and exit code* (~51% of check call sites compare
  captured compiler text); product-keyed simulator builds on
  normalized `.v`/`.ba` bytes; verdict-skip on content identity;
  sims and diffs otherwise always re-run. **Zero `.exp` edits, no
  Shake, no compiler changes** — and it prices at ~4.3× mean work
  reduction over the real commit stream, with roughly half of pushes
  near-free. One compiler-side enabler wanted: a defined `.ba`
  content digest (today the `.ba` unconditionally embeds the build's
  git hash and the full flags record, so byte-identity across
  compiler rebuilds is impossible by construction; `.bo` needs
  nothing — it is already version-free and hash-chains its import
  closure). Two soundness notes outlive the wrapper (v1.2): the
  process boundary it caches at is itself a controlled-effect
  boundary — `(binary, argv, env, files read) → (stdout, exit, files
  written)`, kernel-enforced and mechanically auditable by tracing
  file accesses on misses (the fsatrace discipline Shake's own lint
  mode uses) — which is how *any* cacher polices the tools it shells
  out to; and its weakest keys (`BSC_OPTIONS`, `-cpp` closures, BDPI
  `.c` files) are exactly the inputs only the compiler can report,
  which is why the **input manifest** (RFC v0.23 §3) belongs in bsc
  regardless of orchestrator — reported closures beat inferred ones.
  One trap named while pricing alternatives: a graph orchestrator
  mounted *above* DejaGNU, scheduling whole directories, is a
  strictly worse cache than invocation grain below it —
  directory-grain keys over-invalidate away most of the measured
  win, so "wrap DejaGNU in Shake" is not a stepping stone.
- **Unit/property suites** over the cabalized library are a new,
  cabal-native population orthogonal to the corpus.

What the null hypothesis **cannot** capture is the graph-only
residue, now measurable: the per-pass seam splits (a pre-schedule
elaboration node; genC/genVerilog split out of the fused codegen
invocation) that take the wrapper's ~4.3× to the full ~7.4× — the
fused invocation is the wrapper's ceiling, because a backend-only
change still re-runs FE+elab+sched inside every codegen call; native
verdict nodes and cross-cell leg sharing as the matrix grows (~9–13×
marginal per added cheap leg); per-check scheduling past ~50 cores;
and the deletion of the execution layer. The honest framing for
everything in §4: **the migration is justified only by the graph-only
wins** — and the wrapper raises the bar for what counts as one. An
argument for migration that rests on checker quality or on plain
invocation caching counts value the null hypothesis already banks —
and after the engine's rung 2, plain invocation caching is banked
with **no harness change at all**: the engine caches its own
invocations, subsuming the wrapper's compile leg at reported-closure
soundness and finer grain (§8's revised sequencing). The review round
(v1.3) extends this attribution: two DejaGNU cells requesting
identical nodes from the internal engine get cross-cell dedup and
artifact cutoff *without migration* — so P1–P2's exclusivity claims
below read "impossible without the engine", not "impossible outside
a migrated harness", and the migration's own case rests on verdict
residence, generated legs, scheduling, and layer deletion.

## 4. Pros

**P1 — Cutoff through compiled artifacts.** Verdict nodes hang off
the same content-addressed compile/sim nodes the build uses, so a
compiler change re-runs compiles but sim and compare legs re-run only
where artifacts actually changed. An emitter-neutral bsc change cuts
off every Bluesim leg at byte-identical cxx; the alpha-equivalence
comparator extends the cutoff past naming drift. Today a one-phase
compiler change re-executes all ~48k checks; under the graph it
re-runs the compile sweep plus only the genuinely affected legs.
This requires an engine that *sees* artifacts as nodes — impossible
without the internal engine; available to the un-migrated harness
once it consumes that engine (§3, v1.3).

**P2 — Cross-cell leg sharing.** Differential cells share legs:
trs-vs-Bluesim shares the `.ba`; BVI-via-Verilator vs the oracle
simulator shares the generated netlist; combined-vs-separate shares
the parse. DejaGNU/make re-derives shared work per cell, linearly in
cells — and the differential population is the growing one.

**P3 — Verdict caching in the share (scoped).** A verdict computed
anywhere in the fleet is "(cached) PASSED" everywhere, through the
same share the build runs. Scope condition attached (RFC §16, from
external review): this applies only to checks that have **earned** a
cacheable class — deterministic, hermetic, manifest-complete. What
fraction of the ~48k qualifies is unknown until the cacheability
census runs; this pro is real but its magnitude is **conditional**.

**P4 — A whole layer deletes.** The make+perl execution layer is not
ported; it is deleted — Shake owns parallelism, load balance,
sharding, and aggregation natively — and runtest/expect/tcl leave
the toolchain. The 228 harness procs split cleanly: test *semantics*
(tag checks, filters, comparators) port to typed rules and the S1
checker library, which is the same code either way; execution
*plumbing* vanishes.

**P5 — The semantics layer becomes typed and native.** Structured
verdicts stop being a bolt-on emitter and become the native result
type; checkers become library functions instead of exec'd tools;
check declarations become data the harness validates. Honesty: most
of this pro's *correctness* value is banked by the null hypothesis —
what migration adds is velocity and coherence, not new soundness.

**P6 — The matrix becomes data.** Adding a simulator, engine, or
mode becomes a matrix declaration plus witness rules — legs are
*generated* — instead of per-cell `.exp` edits. The multiplicative
trajectory in §2 is the multiplier on this pro: every new axis
raises the price of hand-enumerated cells and the value of generated
ones.

**P7 — One engine, one share, one mental model.** Build and test
share the caching infrastructure, the remote share, flag oracles,
and the manifest discipline. PR-scoped CI ("run what this change can
affect") falls out at artifact grain — impact analysis for free,
sound by construction rather than by a coverage-map approximation.

**P8 — Hygiene riders.** Uniform per-check timeouts and rlimits;
structured re-run and flake detection (an uncached re-execution is a
first-class operation, not a shell loop); the POSIX-only expect/tcl
dependency drops. Minor individually; free collectively.

## 5. Cons

**C1 — Silent coverage loss across ~48k checks.** The top risk, and
the reason the morning analysis said no. Totals cannot detect a
check that silently stopped existing — the engine-blindness lesson
generalizes to harness migrations. Mitigations are structural:
stable check IDs mapping one-to-one from `.exp` checks to verdict
nodes, and per-directory **dual-run equivalence gates** (old `.sum`
vs new verdict set), themselves differential nodes the graph runs
throughout migration. Translation is mostly mechanical (~757
control-flow constructs in 26,368 lines; the rest straight-line).
Residuals that stay true: the ~757 need human triage; the gates end
someday; and the gate comparator is itself new code that must be
right.

**C2 — Migration cost and the interregnum.** During per-directory
gating, both orchestrators run: CI cost roughly doubles for
migrating directories until their gates retire. The Hadrian warning
applies scaled: GHC's Shake build took years to stabilize —
orchestration is far simpler than a compiler build system, but
"simple Shake project" and "48k-check production harness" are
different claims. And a bespoke harness concentrates knowledge:
"everyone knows make" degrades to "who owns the rules file" — a bus
factor the current stack does not have.

**C3 — The upstream tax, premise-scoped.** With the premise
(upstream-landed), the tax dissolves — the argument is made to
maintainers who already run Shake inside the compiler, and the
complexity burden flips sides: DejaGNU + make + perl becomes the
redundant stack. Fork-only, the tax is permanent and dominant: every
upstream `.exp` change needs translation forever. This con is
therefore not weighed — it is **routed**: it selects which world you
are in (§7a).

**C4 — Test-author accessibility.** Today a hardware engineer adds a
test by writing straight-line Tcl proc calls, knowing nothing of the
harness. If migration makes a Haskell rules file the authoring
surface, upstream test contribution suffers — possibly fatally for
acceptance. This con is answerable but only by design discipline:
per-directory check *declarations* stay data (the same division of
labor as today's 228 procs — authors call, the harness defines), and
Haskell stays confined to the harness. The design document must
treat "test authors never write Haskell" as a hard requirement, or
this con escalates.

**C5 — The self-hosting inversion.** A test orchestrator built by
the toolchain family under test can, in the worst case, be broken by
the very regression it exists to catch. GHC keeps its testsuite
driver in Python for exactly this decoupling. The mitigation is the
RFC's hard rule — **the test orchestrator never links the bsc under
test**: its own executable, built from shake plus at most a *pinned*
bsc library, mostly neither, exercising bsc as a black box (CLI,
diagnostics, artifacts) against an arbitrary install. Residuals: the
orchestrator still rides the GHC/cabal toolchain (platform bootstrap
and GHC upgrades now touch the test stack), and A/B compiler-leg
workflows must be preserved by construction, not by accident.

**C6 — Sound caching is new, permanent machinery.** DejaGNU never
needed cacheability classes, environment manifests, or audit sweeps
*because it never cached* — re-executing everything is trivially
sound. The graph's headline pros (P1–P3) are bought with a standing
discipline (RFC §16, v0.21): every verdict node declares a class;
hermeticity is earned by declaration; manifests attach to verdicts;
periodic uncached audit sweeps run forever. This is real, permanent
process cost — and a new failure mode with fleet blast radius: a
poisoned cached PASS is worse than a slow re-run. The default rule
(unclassified ⇒ non-cacheable; never cache PASS for an incompletely
declared effect surface) caps the severity but not the upkeep.

**C7 — Workflow parity.** The developer loop — `runtest` on one
directory, localcheck, regold — must come out *strictly better*, not
merely equivalent; the morning constraint stands: retire runtest
only if better for every workflow. `.sum` consumers (dashboards,
historical comparisons) need an emitter-compatible output or their
own migration. Neither is hard; both are easy to forget until they
are incidents.

**C8 — What was informal must be specified.** make never enforced
gate ordering, effect surfaces, or hermeticity, so nobody had to
write them down. The graph demands the specification: the gate
ladder, the manifest schema, the check-declaration format. This is
cost now that becomes an asset later (the specification *is* the
documentation the suite never had), but it is cost now.

## 6. The asymmetry — and the precedents on both poles

**What multiplies vs what amortizes.** Price a sweep under both
orchestrators: DejaGNU re-executes Θ(cells); the graph re-executes
Θ(unique stale work). As the matrix grows along its five axes, the
gap widens without bound. Against that: C1, C2, and C8 are one-time;
C3 is routed by the premise; C4, C5, and C7 are design constraints,
paid in the design document rather than recurring. The one genuinely
permanent con is C6 — audits and manifest upkeep never end. So the
steady-state comparison is C6's overhead against P1–P3's savings —
now measured rather than judged (2026-09-29; provenance in the KB
record "bsc testsuite CI economics (measured)"):

- A full sweep costs **4.8 core-hours**; today every push pays 100%.
- Priced over the last 500 real commits with per-pass keys and early
  cutoff (`re-run = S_own + f·S_down`): mean per-push re-run **16%
  on MatX main (~6×) and 13.8% on the development-stream lineage
  (~7×)** at f=5% of downstream artifacts changing (4.3–4.9× at a
  pessimistic f=25%). Per component at f=5%: typechecker ~30%,
  evaluator+scheduler at today's `.ba` seam ~20% (scheduler alone
  ~11% once a pre-schedule node exists), Verilog backend ~6% split
  vs ~19% fused (the genC/genVerilog split's measured payoff),
  C backend ~5%. The scheduler carries an f-floor from its ~71
  textual schedule goldens plus 262 schedule-dump checks.
- The staging ladder: `.bo`/`.ba` caching alone is the trap rung
  (~1.3× — the money is downstream, in simulator builds); the
  orchestrator-neutral wrapper (§3) is ~4.3×; the compiler seam
  splits take it to ~7.4×; each added cheap matrix leg is ~9–13×
  cheaper marginal than a standalone sweep. Parallelism, measured,
  is *not* where the win is: directory-grain LPT already tracks
  work/cores to ~20–40 cores, and even infinite cores floor at ~3
  minutes (the longest single compile) — a ~12× ceiling that
  caching exceeds on the median push of the development-stream
  lineage (MatX main's median re-run is 20%; and the comparison is
  work-cut against a wall ceiling — the two compose rather than
  compete). Labeling note (v1.3): the per-push percentages are
  *modeled* on measured timings (max-bucket pricing slightly
  under-prices multi-component commits versus the union of their
  cones; commits proxy pushes); the timings, counts, and
  determinism facts are measured. (v1.2 re-mapping: under
  engine-first sequencing the wrapper rung's compile-and-product
  caching is delivered by the engine itself — same keys, reported
  rather than inferred, finer than invocation grain — and
  verdict-skip becomes the harness's one thin deliverable; the ~4.3×
  price survives as the value of that pair, whoever implements it.)
- C6's price in these units: one uncached audit sweep is ~5
  core-hours — repaid by a handful of cached pushes.

One honest floor: when the compiler change *does* affect emitted
artifacts, the compile sweep itself still re-runs — cutoff saves the
legs behind unchanged artifacts, never the cost of discovering which
artifacts changed. Front-end changes are therefore the
cache-resistant class (S_own ≈ 26% before any downstream effect),
and the realized win breathes with the roadmap: typechecker-heavy
phases see ~3–5×, backend/scheduler phases ~8–15×.

**The precedents split — and one variable explains the split.**
Bazel is the at-scale existence proof for tests-as-graph-nodes:
cached test verdicts keyed on action inputs, hermetic sandboxing,
per-test size/timeout classes, explicit no-cache/local tags —
the cacheability-class discipline is Bazel's test model rediscovered,
and it works at monorepo scale. On the other pole, GHC runs Shake
for its build and *kept its testsuite in Python*, and LLVM pairs
ninja with lit, a dedicated runner. The variable that explains both
poles: **whether verdicts hang off expensive shared artifacts.**
GHC's tests each compile a tiny fresh program with the just-built
compiler — cells are independent and cheap, so graph residence buys
nothing and decoupling wins. bsc's matrix is the opposite shape:
each cell's compile is expensive, and multiple legs (Bluesim,
Verilog simulators, trs, combined/separate, BVI paths) consume
shared artifacts of that compile — cutoff and sharing are the
dominant structure. bsc's corpus is Bazel-shaped, not GHC-shaped.
That is why "GHC didn't do this" does not settle the question here.

## 7. Conditions that flip the verdict

- **(a) The premise lands fork-only.** C3 applies in full: do not
  migrate the corpus ahead of upstream. Harvest the null hypothesis;
  keep the freeze.
- **(b) The cacheability census comes back hostile.** If the corpus
  is dominantly non-hermetic *and* leg sharing turns out thin, P1–P3
  collapse and the case reduces to P4–P6 comfort wins — not worth
  C1's risk. (The census is cheap and orchestrator-neutral: run it
  first.) *First measured cut (2026-09-29): hostile looks unlikely on
  cost weight.* The work is dominated by compiles and simulator
  builds — hermetic-shaped by construction — while sim runs are <5%;
  the enumerated never-memoize populations are small and principled
  (the staleness-machinery tests that exercise `-u` itself, ~24
  touch/sleep sites; timeout-raced sims; the `Environment`
  date/epochTime tests, whose splices bsc injects unconditionally;
  `$random`-divergent sims already handled by per-simulator goldens).
  Two key-completeness hazards are named for the manifest schema:
  `BSC_OPTIONS` is read at module init and bypasses argv, and `-cpp`
  include files are invisible to the dependency scanner. What remains
  open is the per-check class *assignment* and the manifest schema
  itself.
- **(c) The matrix stops growing.** The asymmetry argument (§6) is a
  bet on trajectory; a frozen matrix weakens it to a wash.
- **(d) C4 proves unresolvable.** If upstream will not accept any
  authoring surface other than today's Tcl, and the data-driven
  declaration design cannot bridge it, acceptance fails regardless
  of technical merit.
- **(e) The dual-run gates disagree beyond mechanical rates.** If
  per-directory equivalence gating finds systematic divergence, stop
  and re-plan rather than push through — the gates exist to be
  believed.

## 8. Verdict and sequencing

Unchanged from RFC §16, restated with this document's weights:
**yes — conditional on the upstream premise, sequenced after the
internalized engine (rung 2) is proven, gated per-directory by
dual-run equivalence, with the cacheability discipline in force from
the first migrated check.** The trigger is "the engine landed," not
a date.

Independent of the trigger, the now-list — revised v1.2 to
engine-first, superseding v1.1's wrapper-first ordering: with the
engine direction settled, build *toward* rung 2 rather than around
it, and let the testsuite be the engine's second consumer.

1. **The identity layer, as the engine's first milestone**: the `.ba`
   content digest (skip the embedded version string, canonicalize the
   serialized flags; `-remap-path-prefix` already covers paths); the
   **input manifest** — bsc reporting the true closure it read
   (sources and imported `.bo`s, the post-`-cpp` file set, the
   `BSC_OPTIONS` contribution, BDPI `.c` files), reported from inside
   rather than inferred from outside; and the flag-partitioning
   table. The hard part of wrapper and engine alike; everything later
   consumes it. The fingerprint unit is fixed (v1.3): three producer
   components as private cabal sublibraries — .bo/.ba (coupled
   production), .v, and .cxx/.h — over supporting components, with
   per-component fingerprints derived from the cabal component graph
   and embedded in the shipped compiler; never a git revision or GHC
   ABI hash.
2. **The `-u` replacement with a persistent, invocation-wide cache**
   (RFC §3 with the v0.23–v0.24 requirements), proven on bsc's own
   build first — the low-risk deployment that hardens keys where
   failures are obvious, and a build already half-prepared: the **B0
   manifest** (bsc.cabal + cabal.project on release-devel-B0) ships
   the cabalized tree with executables as thin clients, so the
   packaging delta is the sublibrary carve, and the library build is
   `.bo`-only, so its selective reuse needs no `.ba` format work.
   The testsuite analysis adds four requirements to the driver spec:
   probes under **every** compile entry point (the suite's compile
   lines mostly do not use `-u`); **byte-identical diagnostic
   replay** on hits, including the *merged* stdout/stderr transcript
   as captured (~51% of check sites compare captured text; separately
   stored streams can replay a different interleaving); coverage
   **through the link stages** (`bsc -e`'s C++ compile+link and the
   simulator builds it spawns are the two largest measured buckets —
   a compile-only cache strands them); and a **recursive cache-bypass
   channel** carrying test intent, honored by every cache layer — a
   performance or staleness test that re-runs over a silently cached
   inner invocation measures a lookup, not the compiler. With these,
   the un-migrated suite inherits compile/link caching the day the
   engine lands, with no `.exp` edits — the never-memoize populations
   additionally need the bypass wiring.
3. **The harness verdict layer**: verdict-skip and sim-run skip on
   input-closure identity, keyed by engine-native identities — the
   residue no compiler-side engine can subsume (the compiler cannot
   know what a check *means*), permanent in every ordering, thin once
   items 1–2 exist, and native verdict nodes after any migration. Its
   soundness net stays the periodic uncached sweep — the same audit
   C6 requires forever, built early, now mechanized by diffing input
   manifests against traced file accesses, with its **cadence priced
   against total traffic** rather than asserted (one full audit costs
   a sweep; at main-only cadence a daily audit would cost more than
   caching saves — PR/dev traffic sets the rate), and bypassing
   *every* cache layer, not just verdict lookup.
4. **The S1 checker tools and structured-verdict emitter** (the
   semantics layer either way) and the **stable check-ID scheme**
   (the S1 emitter and the migration both need it — design it once).
5. **The cacheability census completion** (it prices P3 and arms flip
   condition b): the cost-weighted first cut is done (§7b); the
   per-check class assignment and manifest schema remain — the
   verdict manifest now defined as a closure over item 1's input
   manifests, not a third notion.

**The wrapper is the contingency, not a step.** If the engine's
landing leaves the measured 4–6× unbanked too long — the interim rent
is ~5 core-hours of compute and a 36-minute wall per push — the §3
wrapper is the weeks-scale patch, and items 1 and 3 transfer into it
unchanged; what retires at engine-landing is only its interposition
shim. That is a scheduling judgment, not an architecture question,
and it is the only place v1.1's ordering survives.

The mechanism-level design document (rule vocabulary, verdict schema,
`bsc-test` shape under the never-link rule, the `.exp` translation
plan, the check-declaration format answering C4) is the next artifact
after this one; it can precede the trigger, since the revised
staircase's S3 is "a rules file over the existing engine."

## 9. Relation to prior records

- `RFC-bsc-artifact-graph.md` §16 (v0.23) — the normative record
  this document expands: the four mechanisms (P1–P4 here), the three
  re-priced cons (C1, C3, C5), the cacheability classes and gate
  ladder (C6, C8, P3's scope), and the sequencing. The RFC governs
  on divergence.
- The 2026-08-23 morning analysis (DejaGNU vs Cabal) — the
  superseded question; its census (§2 here), its structural cons,
  and its S0–S4 staircase remain this document's factual baseline.
- External review (Codex, 2026-08-23, KB lane) — the cacheability
  and gate-ordering objections adopted into RFC v0.21 and priced
  here as C6/C8 and P3's scope condition.
- "KB: bsc testsuite CI economics (measured)" (2026-09-29) — the
  measured record behind v1.1's numbers: per-command CI timing, the
  component re-run matrix, the commit-stream pricing on both
  lineages, the ccache cold-cache finding with its retraction trail,
  and the in-tree mechanics audit (chokepoints, determinism,
  `.bo`/`.ba` serialization, never-memoize populations); its
  2026-09-30 addendum records the engine-first sequencing decision
  behind v1.2.
- "KB: REVIEW REQUEST — bsc engine-first proposal (adversarial)"
  (2026-09-30) — ChatGPT's adversarial review round (two blockers
  adopted; economics relabeling; attribution correction; engine
  scorecard additions) and the response blocks recording the
  B0-manifest baseline, the resolved legacy option, and the
  `.bo`-only library path.
- "bsc orchestration and rebuild implementation plan", Revision 2
  (ChatGPT; native Google Doc, Markdown copy in Drive, full Revision 1
  text in the review-request draft) — the delivery vehicle of record
  for the engine-first sequence, read with this round's corrections.
- The KB lane draft "KB: bsc artifact graph" — the session-entry
  history behind all of the above.
