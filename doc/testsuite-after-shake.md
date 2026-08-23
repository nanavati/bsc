# The Testsuite After Shake: Pros and Cons

Should the testsuite follow the compiler onto Shake — the full weighing.

**Status:** Analysis v1.0 — 2026-08-23 (Ravi Nanavati with Claude).
Written as the decision-support expansion of
`RFC-bsc-artifact-graph.md` §16, which answers this question in
compressed, normative form (yes — conditional, sequenced, gated). This
document weighs both sides at full strength: the pros with their
scope conditions attached, the cons at their strongest, the null
hypothesis priced separately, the precedents on both poles, and the
conditions under which the verdict flips. On any divergence, the
RFC's current revision governs; this document argues, the RFC
records. Not proposed upstream.

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
- **ccache works now** (bsc takes the C++ compiler from `CXX`), and
  naming determinism raises its hit rate — no harness involvement.
- **Unit/property suites** over the cabalized library are a new,
  cabal-native population orthogonal to the corpus.

What the null hypothesis **cannot** capture is exactly the graph-only
set: artifact-grain cutoff, cross-cell leg sharing, sound verdict
caching, and the deletion of the execution layer. The honest framing
for everything in §4: **the migration is justified only by the
graph-only wins.** An argument for migration that rests on checker
quality counts value the null hypothesis already banks.

## 4. Pros

**P1 — Cutoff through compiled artifacts.** Verdict nodes hang off
the same content-addressed compile/sim nodes the build uses, so a
compiler change re-runs compiles but sim and compare legs re-run only
where artifacts actually changed. An emitter-neutral bsc change cuts
off every Bluesim leg at byte-identical cxx; the alpha-equivalence
comparator extends the cutoff past naming drift. Today a one-phase
compiler change re-executes all ~48k checks; under the graph it
re-runs the compile sweep plus only the genuinely affected legs.
This requires the orchestrator to *see* artifacts as nodes —
structurally impossible from DejaGNU's position outside the graph.

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
steady-state comparison is C6's overhead against P1–P3's savings; at
~48k checks with the differential population growing, one avoided
full sweep plausibly pays for a long period of audit overhead
(order-of-magnitude judgment, to be replaced by census numbers).
One honest floor: when the compiler change *does* affect emitted
artifacts, the compile sweep itself still re-runs — cutoff saves the
legs behind unchanged artifacts, never the cost of discovering which
artifacts changed.

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
  first.)
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

Independent of the trigger, three things are worth doing now because
they are orchestrator-neutral and de-risk both worlds: the S1
checker tools and structured-verdict emitter (the semantics layer
either way), the **cacheability census** (it prices P3 and arms flip
condition b), and the **stable check-ID scheme** (the S1 emitter and
the migration both need it — design it once). The mechanism-level
design document (rule vocabulary, verdict schema, `bsc-test` shape
under the never-link rule, the `.exp` translation plan, the
check-declaration format answering C4) is the next artifact after
this one; it can precede the trigger, since the revised staircase's
S3 is "a rules file over the existing engine."

## 9. Relation to prior records

- `RFC-bsc-artifact-graph.md` §16 (v0.21) — the normative record
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
- The KB lane draft "KB: bsc artifact graph" — the session-entry
  history behind all of the above.
