# Handoff: the typechecker coherent-instances PR stack

*2026-07-10.  State of the effort to upstream the
`claude/typechecker-coherent-instances-dkmn8w` branch (nanavati/bsc) into
B-Lang-org/bsc as a stack of reviewable PRs.*

## The stack at a glance

```
upstream main (d2f996c0)
├── PR1  #1032  claude/instance-trie-fixes        OPEN     4 commits  d38778e0
├── PR-A #1033  claude/coherence-keywords-coverage OPEN     4 commits  3e91add7
│   (independent of PR1; both merge into the integration base)
└── integration base 20271cb1 = main + PR1 + PR-A (linearized)
    └── PR2  claude/ordered-clause-commitment     SEALED   7 commits  ff278307
        ├── PR3  claude/sat-batching-settlement   PUSHED   2 commits  d8a5cab9
        ├── PR6  bound-variable discipline        NEXT CARVE (parallel to PR3)
        └── PR4  solved-dictionary pool           LAST (needs PR3 + PR6)
```

PR bodies ready to paste: `pr2-body.md`, `pr3-body.md` in the session
scratchpad (also previously delivered as downloads).  PR2/PR3 have **not**
had `gh pr create` run yet.  PR3's body references PR2 by branch name;
swap in `#NNNN` once PR2 is opened.

## What each PR contains

### PR1 — instance-trie fixes (#1032, open)
Fixes instance-trie ordering and probing holes that broke coherence
detection (sortLeaf total-map lookup, legacy-index StuckATF variant).
Pins: `bsc.typechecker/instances/order` (LeafOrder, LeafOrderChain,
FdStability, FdOrder, TFunHead).  Fully independent of PR-A.

### PR-A — coherence keywords + coverage warning (#1033, open)
BSV soft keywords `coherent`/`incoherent` for typeclasses (Classic has had
them since open-sourcing; this is parser + symbol-table plumbing), the
T0160 fundep-coverage warning, and the hidden
`-incoherent-instance-matches` toggle (default off).  `incoherent`
suppresses T0160; `coherent` forbids unforced selection regardless of the
flag.  Docs: BSV/BH grammar + annotation + coverage sections.
Pins: coverage-warning and keyword tests.

### PR2 — ordered-clause commitment (SEALED, ff278307)
The semantic core. Seven commits, born-in-place history:

1. `91a67022` Give the constraint solver's results proper types —
   `data Match a = NoMatch | Conflict | Match a` + `firstMatch` +
   `matchFDRow` row core; records `SatResult` (with `Commitment`:
   `Committable | Provisional`), `SolveResult`, `Reduction`, `InstMatch`.
   Pure refactor, no behavior change.
2. `8001b1b7` Ordered-clause fundep semantics: outputs never bar a match.
3. `11f19c0d` Commit coherent instance matches by default, with predicate
   ancestry (the commitment machinery; `earlierInstanceMayCapture` modal
   check; incoherent classes + `-legacy-defer-instances` keep fall-through).
4. `3056de98` Report ordered-clause fundep conflicts (T0159), failing fast
   when final (`matchTopIsReducible`, `findFunDepConflict`).
5. `8f809755` Keep diagnostics rooted, positioned, and complete under
   commitment (position carrying in reportedPwp, EBadIfcType position
   fallback, self-contained "could also be deduced" hints, fail-fast
   deferral to the definition-level report; regenerated goldens for
   gh221/gh894/BuildList/BuildVector/noinline/signature, b1225 restored).
6. `08e6966c` testsuite: ordered-clause commitment pins
   (`bsc.typechecker/instances/commit`).
7. `ff278307` Document coherent instance selection in the user-facing
   guides (BSV/BH ref guides + user guide; note BH_lang.tex is latin-1).

### PR3 — SAT batching + settlement (pushed, d8a5cab9)
2 commits on PR2. Removes the per-predicate proviso-SAT fallback in
`reducePred`; numeric residuals stream to a single settlement point per
definition (`batchSolveNumericPreds`: one solver session per batch,
`tsNumProven`/`tsNumRefuted` caches in TIMonad).  Owners: `tiExpl'''`,
verdict-complete `satisfy`/`satisfyFV` (new `satisfyStream`/`satisfyFVStream`
for callers that own a later settlement point), the incoherent-match
full-vs-partial verdict, `tryDefault`.  Carries the b675 ICE fix
(`SolvedBinds.addBindDeps`).  Measured on FloatingPoint.bsv: 501 → 24
solver sessions, 1418 → 115 queries, −26% wall clock.
Pins: `bsc.typechecker/numeric-settle`, each certified solver-only by a
dual variant (fails with `-no-use-proviso-sat`, passes with it): the
obligation is cross-class entailment `Mul#(a,2,b) ⊢ Add#(a,a,b)`.

### PR6 — bound-variable discipline (to carve; content proven on dev-port)
`mgu` refuses to substitute bound (rigid) type variables at value kinds;
rigid fundep improvements defer instead of conflicting.  On the unified
type this is: `Match a` gains a `Defer` arm, `matchFDRow` discriminates
guarded-vs-unguarded unification failure, `firstMatch` ranks
Match > Conflict > Defer > NoMatch, and the commitment gate/probes make
their modal checks unguarded (`predUnify []`).  Plus T0161 skolem-escape
rejection at generalization, `_tc` temporary suppression in EUnify.
Pins: higherrank skolemization, bound-type-vars goldens, ModalCapture,
noinline/signature T0043 golden updates.
Carve by replaying the dev branch's first six commits above PR3
(`04e277c6..6d19cdb4`) onto ff278307.

### PR4 — solved-dictionary pool (last)
SolvedBinds ordering at emission; intra-pass `solved` sharing through
sat/satMany; cross-pass EPred pool (propagateFunDeps no longer discards);
non-ground pool entries; closed-certificate hardening + diagnostics;
`markIncoherent` (information-dependent choices never pooled); modal pool
guard.  Pins: `bsc.typechecker/dictpool`, vector_interfaces golden.
Already adapted onto the records refactor on the dev branch (commits
`1cfc8a59..dd16eae9`); carve by replaying those seven commits.

## Verification state

- PR-A: full suite sealed earlier (18,138 passes; 3 environment artifacts).
- **PR2 SEALED at ff278307: full suite 18,117 passes, 0 regressions** —
  the only failures are the three file-permission tests that always fail
  running as root (b1595 ccomp, driver/imports UnreadableTop,
  preprocessor/include DupInclude).
- PR3: full `bsc.typechecker` tree + numeric-settle dual variants green
  at its tip.
- Dev branch (port): build green; sweep (full typechecker tree +
  vector_interfaces, getput, b675, SquareRoot) 1,519 passes / 0 fail;
  endpoint tree verified byte-identical through the final restack.
- Testsuite hygiene: always scrub untracked artifacts before a run
  (`git ls-files --others testsuite | xargs rm -f`); stale `.bo` files make
  `bsc -u` skip recompiles and poison compare_file/warning-count tests.
- Run the suite with the MATCHING install: the run-suite-*.sh wrappers pin
  BSC per worktree — a mismatched wrapper invalidates the whole run.

## Pending / known issues

1. PR2 and PR3 are ready to open (`gh pr create` commands below); PR3's
   body needs PR2's `#NNNN` substituted once PR2 is opened.
2. `-Wall` cosmetics, non-blocking: the new records' selectors are unused
   (warning), and the `anyTExpr` import is unused (pre-exists upstream;
   the dev branch removes it in the pool commit).
3. Dev branch is fully ported and pushed (`1b35eb7d`): PR3 tip + PR6
   content + pool commits adapted to the records types + dev note.  The
   old dev tip is preserved locally as `backup-dev-pre-port` (26f5493e)
   in /home/user/bsc.
4. PR6 carve is next (six commits, content already proven on the dev
   branch), then PR4 (pool, five commits + modal-guard fix).
5. A full-suite seal has not been re-run on the ported dev branch (its
   sweep is green and its tree is byte-identical to the validated
   endpoint); run one before treating dev as sealed.
6. Ledger (not started): poly-kinded TypeEq stage 2; stage-1 wall-clock
   profiling; misc.

## Conventions (do not drop)

- Author on every commit: `Ravi Nanavati <ravi@matx.com>` (pass
  `--author` explicitly; repo config committer is Claude for verified
  badges).
- Every commit message ends with the `Co-Authored-By: Claude Fable 5
  <noreply@anthropic.com>` and `Claude-Session:` trailers.
- Never put the model id in commits, PRs, or code.
- Gates before any push: build + typechecker sweep (+ targeted dirs);
  full suite before calling a branch sealed.
- The dev note (`doc/dev-notes/typechecker-coherent-instance-commitment.md`)
  ships on the dev branch only — PR carves exclude it; it can be attached
  to a PR as a file.
- Armed sweeps: pass extra flags via `BSC_OPTIONS` (the harness normalizes
  a `BSC="path -flag"` override away).

## Where things live

- `/home/user/bsc` — dev repo; branch `dev-port` (port in progress),
  `claude/typechecker-coherent-instances-dkmn8w` (dev, untouched until the
  port validates).  Remotes: origin=nanavati/bsc, upstream=B-Lang-org/bsc.
- `/home/user/bsc-pr2`, `/home/user/bsc-pr3`, `/home/user/bsc-pra` —
  per-PR clones with their own `inst/` installs.
- Scratchpad (`/tmp/claude-0/.../scratchpad`): `run-suite-{pra,pr2,pr3}.sh`
  (env wrappers pinning TEST_CONFIG_DIR/BLUESPECDIR/BSC per install),
  `fullsuite-*.sh`, `pr2-body.md`, `pr3-body.md`, commit-message files
  (`msg-*.txt`), the design note
  (`design-note-coherent-commitment.md`).

## Opening the PRs (when ready)

```sh
# PR2 (after the comment restack and a green full suite)
gh pr create --repo B-Lang-org/bsc \
  --head nanavati:claude/ordered-clause-commitment \
  --title "Ordered-clause fundep semantics: commit coherent instance matches" \
  --body-file pr2-body.md

# PR3 (swap the branch reference in the body for PR2's #NNNN first)
gh pr create --repo B-Lang-org/bsc \
  --head nanavati:claude/sat-batching-settlement \
  --title "Settle numeric provisos once per definition, in one SAT session" \
  --body-file pr3-body.md
```
