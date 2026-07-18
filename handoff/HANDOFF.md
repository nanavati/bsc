# Handoff: ioprops PR pair — status and remaining step

## Status: both upstream PRs are OPEN and properly stacked

- PR 1: https://github.com/B-Lang-org/bsc/pull/1059 — the getIOProps
  inout-feedthrough fix (base `main`, head `claude/ioprops-inout-fix`).
- PR 2: https://github.com/B-Lang-org/bsc/pull/1060 — semantic port
  properties (base `claude/ioprops-inout-fix`, head
  `claude/vioprops-apackage-3pmbya`).

The head branches live in B-Lang-org itself, so updating a PR means
pushing to the branch **in B-Lang-org**, not the nanavati fork.

## One remaining step

The remote session validated PR 2's head with a full-testsuite gate and
found one more stale golden of the b302 class:
`testsuite/bsc.bugs/bluespec_inc/b569/mkAddSub.v.expected`
(generated-name counter drift; the comparison only runs where a Verilog
simulator is configured). The regenerated golden is commit `d802fc1c`
on the fork's `claude/vioprops-apackage-3pmbya` (validated: portprops
87/87, b569 and b302 green). Bring it into PR 2:

```sh
git fetch git@github.com:nanavati/bsc.git claude/vioprops-apackage-3pmbya
git push git@github.com:B-Lang-org/bsc.git FETCH_HEAD:refs/heads/claude/vioprops-apackage-3pmbya
```

(Fast-forward: one commit on top of the current PR head 01d6c070.)

## After PR 1 merges

Retarget PR 2's base to `main` (automatic if the base branch is deleted
on merge).

Remote session: https://claude.ai/code/session_01EajBnZQ1gitQ1wXz5h6jky
