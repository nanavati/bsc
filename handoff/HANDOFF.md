# Handoff: open the stacked ioprops PRs on B-Lang-org/bsc

You are Claude running on Ravi's laptop with his GitHub credentials. Your job
is only the credential-requiring steps: pushing two branches to
`B-Lang-org/bsc` and opening two stacked PRs. All engineering work happens in
a remote Claude session against the `nanavati/bsc` fork; do not redo it.

This document and the PR bodies live on the fork, on the docs-only branch
`claude/ioprops-handoff` (directory `handoff/`; never push this branch
upstream). Fetch the latest before acting -- the remote session updates it,
in particular `pr2-body.md`, whose validation numbers are refreshed when the
PR-2 branch is force-pushed:

```sh
git fetch origin claude/ioprops-handoff
git show origin/claude/ioprops-handoff:handoff/HANDOFF.md
git show origin/claude/ioprops-handoff:handoff/pr1-body.md > pr1-body.md
git show origin/claude/ioprops-handoff:handoff/pr2-body.md > pr2-body.md
```

Remote session (for the human to check progress):
https://claude.ai/code/session_01EajBnZQ1gitQ1wXz5h6jky

## The two PRs

1. **`claude/ioprops-inout-fix`** — a small bugfix to `getIOProps`
   (src/comp/VIOProps.hs): the interface-inout definitions (`io_ds`) were
   missing from its use tracking, so an argument inout re-exposed at an
   interface inout was mislabeled `unused`. Two commits: the fix + tests
   (`InoutProps_ArgToIfcHier`, `InoutProps_TwoArgToIfc`,
   `InoutProps_ArgToSubIfc` and golden updates). Based on upstream `main`
   (941eecf). **Ready now.**

2. **`claude/vioprops-apackage-3pmbya`** — semantic port properties
   (`getIOPropsA`): derive `clock`/`reset`/`reg`/`const`/`unused` from the
   APackage + schedule instead of measuring the optimized netlist; feed the
   `.bo` wrapper attributes for both backends (Bluesim gains port props) and
   the Verilog "Ports:" comment; keep `getIOProps` behind `-dIOproperties`
   for comparison. Includes a design doc (`doc/proposals/port-properties.md`),
   new golden tests, and regenerated goldens.
   **NOT ready yet**: it currently sits on April main (e7d44bf6) and is being
   rebased/ported in the remote session onto `claude/ioprops-inout-fix`
   (upstream moved 121 commits, including the `vf_output` → `vf_outputs` /
   `vf_inputs :: [[VPort]]` Method restructuring that this code mirrors).
   The remote session will force-push the same branch name on the fork when
   the port is validated.

## Steps

### A. PR 1 (do now)

```sh
git clone git@github.com:nanavati/bsc.git bsc-fork && cd bsc-fork   # or fetch in an existing clone
git fetch origin claude/ioprops-inout-fix
git push git@github.com:B-Lang-org/bsc.git origin/claude/ioprops-inout-fix:refs/heads/claude/ioprops-inout-fix
gh pr create --repo B-Lang-org/bsc \
  --base main --head claude/ioprops-inout-fix \
  --title "Fix getIOProps: an inout argument exposed at an interface inout is live" \
  --body-file pr1-body.md
```

`pr1-body.md` is provided alongside this doc (drop its "opened on the fork"
footnote if present). Record the PR number — call it **N1**.

### B. PR 2 (only after the fork branch is re-based — verify first)

Verify the rebase has landed before pushing:

```sh
git fetch origin claude/vioprops-apackage-3pmbya claude/ioprops-inout-fix
git merge-base --is-ancestor origin/claude/ioprops-inout-fix \
    origin/claude/vioprops-apackage-3pmbya \
  && echo READY || echo "NOT YET - the fork branch has not been re-based"
```

If NOT YET, stop; the remote session hasn't finished. When READY:

```sh
git push git@github.com:B-Lang-org/bsc.git origin/claude/vioprops-apackage-3pmbya:refs/heads/claude/vioprops-apackage-3pmbya
gh pr create --repo B-Lang-org/bsc \
  --base claude/ioprops-inout-fix --head claude/vioprops-apackage-3pmbya \
  --title "Semantic port properties: derive from the APackage, feed every backend" \
  --body-file pr2-body.md
```

Before submitting, edit `pr2-body.md`: replace the "Based on #10" line with
"Based on #N1" (the upstream PR number from step A), and drop the
"opened on the fork" footnote.

### C. After PR 1 merges

If the base branch is deleted on merge, GitHub retargets PR 2 to `main`
automatically. Otherwise retarget PR 2's base to `main` by hand. Either way
the PR 2 diff collapses to the semantic work alone.

## Notes for CI / review questions

- The full dejagnu testsuite was run remotely (SYSTEMCTEST=0). The only
  remaining failures are tests requiring unreadable files while running as
  root (`bsc.driver/imports` UnreadableTop, `b1595`, `DupInclude`) — an
  environment artifact, not a change effect.
- PR 2 regenerates golden `.v` files in two categories: "Ports:" comments
  (the semantic labels are richer), and ~15 goldens whose `compare_verilog`
  checks only run when a Verilog simulator is configured — those had rotted
  (generated-name counter drift, `__hN`/`___dN`) before this branch, verified
  with a pre-change compiler. If upstream CI has no Verilog simulator, the
  latter never run there.
- History note: both fork PRs (nanavati/bsc #10, #11) for this work were
  closed in favor of these upstream ones.
- Do not open PR 2 with base `main`: the branch deliberately contains the
  fix commits, and the stacked base is what keeps its diff clean.
