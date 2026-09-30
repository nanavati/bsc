# bsc four-sublibrary carve: gate brief

You are a bsc gate session on this machine. Execute this brief exactly.
The three patch files and SHA256SUMS sit in the same directory as this
file; call that directory $PATCHES below.

Standing rules: never open a pull request; never push to any branch except
claude/bsc-testsuite-cabal-dejagnu-cscgl9 on MatX-inc/bsc (create it there
if absent); never weaken, skip, or disable a check to make a gate pass.
Plan discipline: after patch 0001 applies, doc/engine-first-plan.md in the
tree is the plan of record -- these are packaging-only changes with no
behavior change. If a gate exposes a design-level problem rather than a
mechanical build error, STOP and write the report; do not redesign.

## Setup

1. WORK=$HOME/bsc-gates. Clone MatX-inc/bsc there (never reuse a working
   checkout someone may be editing). cd "$WORK".
2. git fetch origin release-devel-B0 and verify its tip commit is 9306c345.
3. If origin already has claude/bsc-testsuite-cabal-dejagnu-cscgl9, check
   it out and skip any patch below whose commit is already present.
   Otherwise: git checkout -B claude/bsc-testsuite-cabal-dejagnu-cscgl9 9306c345
4. (cd $PATCHES && sha256sum -c SHA256SUMS) must pass. Then:
   git am $PATCHES/0001-*.patch $PATCHES/0002-*.patch $PATCHES/0003-*.patch

Series context: 0001 carves bsc.cabal into four private sublibraries
(bsc-common 143 modules, bsc-semantic 71, bsc-verilog 14, bsc-bluesim 22)
under a public facade library that re-exports the identical 250-module
surface, and retargets SetupHooks.hs (generated-module rules, Tcl link
configuration, solver rpath) to bsc-common. 0002 adds util/rebuild-bench,
the P0 measurement harness. 0003 adds the bscdeps executable (machine-
readable dependency discovery) plus an additive export-list change in
src/comp/Depend.hs. The series was written without a Haskell toolchain and
has never been compiled: expect mechanical cabal/GHC errors. Your job is
minimal fixes -- one commit per fix, quoting the compiler error verbatim in
the commit message.

## Gates, in order

G1  cabal build  (all four sublibraries, the facade, every executable
    including bscdeps). If a module sits in the wrong sublibrary, move its
    name between the sublibrary stanzas; the facade's reexported-modules
    list must remain exactly the original 250 names throughout.
G2  make -C src/Libraries build install, using the cabal-built bsc.
    Confirm the installed Libraries layout matches a pre-series build of
    plain release-devel-B0 (build that once first, as the oracle; never
    modify the make path).
G3  bscdeps sanity: from src/Libraries/Base3-Contexts run the built bscdeps
    with that directory's make flags
    (-stdlib-names -bdir <BUILDDIR> -p . -vsearch <BUILDDIR>) on
    Contexts.bsv; spot-check the pkg/imp/probe lines against what
    bsc -u actually touches there.
G4  util/rebuild-bench/bench.sh null clean-outputs verilog-edit
    library-edit   (the full scenario set if time allows). Keep
    bench-results/.
G5  cabal test smoke, then cabal test utils. Run the full DejaGNU suite
    only if asked; otherwise record it as pending in the report.

## Finish

Push the branch (series plus your fix commits) to MatX-inc/bsc. Write the
per-gate report -- pass/fail, wall and CPU time, every fix commit with the
error it fixed, and the bench-results summary -- to bsc-gate-report.md in
the parent directory of $WORK, and print it in full. Use your own session's
commit conventions; keep messages plain.
