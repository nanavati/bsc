# Compiler library boundaries

This structural layer builds on the Cabal conversion in PR #1084. It preserves
that compiler's `.bo` and `.ba` formats and normal read/write workflow. The
module boundaries below are in-memory Haskell APIs; this change introduces no
additional artifact format or build orchestration system.

There are **16 component libraries**: ten compiler/driver libraries, three solver
libraries, the legacy `.ba` codec, and the independent `htcl` and `waveforms`
libraries. Excluding the solvers and legacy codec leaves twelve libraries,
including the two reusable tooling libraries. The `bsc` compatibility facade and
`bsc-setup` build-hook library are additional packaging components, not compiler
phases.

| Package | Ownership |
| --- | --- |
| `bsc-common` | Shared compiler representations, pure utilities, diagnostics, option enums and phase configuration records; unscheduled `AModule` |
| `bsc-parse` | Preprocessing and parsing |
| `bsc-typecheck` | Source preparation, typechecking and internal conversion |
| `bsc-package` | Existing `.bo` codec, imported-package reading and foreign declaration processing |
| `bsc-elab` | Elaboration and cleanup before scheduling |
| `bsc-scheduled` | Static schedule/resource-allocation types, `ASModule`, neutral `ABin` values and resolved module hierarchies |
| `bsc-schedule` | Scheduling, resource allocation, path checks, proofs and schedule diagnostics |
| `bsc-verilog` | Verilog lowering, netlist types, optimization, physical port analysis and generation |
| `bsc-bluesim` | Bluesim lowering and generation from resolved module inputs |
| `bsc-driver` | Invocation-wide flags, CLI decoding, Git provenance, dependency discovery and orchestration adapters |
| `bsc-stp` | Independent STP binding and native linkage |
| `bsc-yices` | Independent Yices binding and native linkage |
| `bsc-sat` | Compiler-to-solver translations, disjointness and SAT services |
| `bsc-legacy-ba` | Existing `.ba` reader/writer, exact wire instances and compatibility options |
| `htcl` | Independent Tcl binding and C shim |
| `waveforms` | Independent VCD reader and formatter |

## Types at the boundaries

`PhaseConfig phase` carries that phase's options plus shared diagnostic and
observation settings. Only the driver owns the complete `Flags` record and its
projections in `PhaseConfigDriver`; compiler libraries do not import either.
`CompilerVersion` is a neutral metadata record passed explicitly where the existing
compiler output observes version information; it has no generated Git dependency.
Only driver-owned `Version` constructs it from generated `BuildVersion`. This
keeps repository revision out of phase-library implementation identities while
preserving version-bearing output and language-visible version constants/macros.
Solver translation APIs receive `SATFlag` directly. The STP/Yices bindings have
no compiler dependencies, leaving room to replace their local implementations
with external Cabal packages.

The driver groups its existing scheduling sequence into:

```haskell
scheduleModule :: ErrorHandle -> Flags -> DumpNames -> TimeInfo -> AModule
               -> IO (TimeInfo, ASModule)
```

`AModule` contains an elaborated body with its source identity/type/pragmas.
`ASModule` contains the scheduled body, schedule/resource facts, wrapper schedule,
method diagnostics and path information. This grouping retains the original
order of scheduling, schedule-definition insertion, proofs and path checks.
Neither wrapper has a serialization instance. `StaticSchedule` belongs to
`bsc-scheduled`; lowered `ASPackage` netlists and their operations belong to
`bsc-verilog`.

Bluesim receives an already loaded hierarchy:

```haskell
simExpand :: ErrorHandle -> PhaseConfig BluesimGenFlags -> ResolvedHierarchy
          -> IO SimSystem
```

Artifact loading is supplied by the application to the driver's loader. Both
backends own their existing noinline, conflict-wire, assumption and unspecified
value lowering. The implementations retain the baseline transformations and
execution order. This deliberately duplicates small existing passes so a change
to one backend need not invalidate the other backend's library closure.

## Existing serialization

The `.bo` implementation remains `GenBin`. The old `.ba` reader and writer share
`bsc-legacy-ba`; their format-specific instances are split into source modules
within that same package. `LegacyABin` pairs the neutral compiler value with the
frozen serialized options and optional Verilog program. The app-local adapter
converts global `Flags` to/from those compatibility fields. Their order, tags,
header and existing lossy schedule encodings remain the baseline wire contract.

The facade does not reexport the legacy codec. The compiler executable, Bluetcl,
`dumpba` and `showrules` depend on it explicitly, retaining their existing `.ba`
read/write behavior. Phase libraries and shared schedule representations do not
depend on that codec. No replacement format is introduced in this layer.

## Dependency and fingerprint scope

The manifest is a source ownership map and an explicit import DAG. The parser
and typechecker have separate package identities. The `.bo` producer's library
closure contains `common`, `parse`, `typecheck`, `package` and the solver stack;
it excludes elaboration, schedules, backends and `.ba` implementation. Scheduling
depends on shared schedule types and solver services, with neither backend in
its closure. Each backend can consume schedule values without depending on the
current scheduling algorithm or its peer backend. Codecs depend on data and
binary primitives, not phase implementations.

`bsc-common` intentionally groups shared utilities and compiler IR rather than
making every data module a package. `bsc-scheduled` is separate because parsing,
typechecking and `.bo` production do not need static schedule representations.
A future alternate scheduler can provide another contract without forcing its
algorithm into existing frontend libraries. This is a useful dependency cut,
not a claim that the current static schedule type is a universal scheduler IR.

These boundaries support separate package fingerprints. They do not by
themselves make phases hermetic or implement a cache: observation settings,
ambient compiler inputs and dependency contents still need to be included by
any future cache implementation.

## Maintaining the graph

Edit `util/recabal/manifest.json` and source ownership together, then run:

```sh
python3 util/recabal/gen.py generate
python3 util/recabal/gen.py verify --strict
python3 -m unittest discover -s util/recabal -p 'test_*.py'
```

The generator writes component Cabal files, isolated source symlink farms,
project configuration and the facade reexports. Verification checks complete
ownership, import edges, phase/configuration cuts, generated-file fixed points
and component-local `Warmup` roots. Negative regression tests exercise the cuts
by introducing forbidden dependencies.

The shared setup hook retains the build layer's local generated modules and
parallel-build barrier. Each component's source roots import its own generated
`Warmup`; `BuildSystem` belongs to `bsc-common`, while `BuildVersion` is generated
only for `bsc-driver`. The version rule tracks its generator, source Git identity
and configured version-policy flags. `no-git` and `no-update-build-version` belong
to `bsc-driver`; `stp-stub` and `yices-stub` belong to their binding packages.
The Make adapter translates
the corresponding environment aliases into these tracked Cabal flags. Native
source edits are dependencies of the binding's demanded `Warmup` rule, while Git
metadata is tracked only by hooks and never listed as distribution source.
These component source farms assume a repository checkout; this change does not
claim each component is a standalone source distribution. GHC 9.14.1 and newer use parallel Cabal/GHC
builds, the shared job semaphore and object determinism. Older supported GHCs
use one Cabal worker, one GHC worker and no semaphore. Both paths retain the
component-local loading barrier. Native solver and Tcl
link configuration belongs to their adapters rather than the shared compiler
substrate.

Each compiled component also receives a private package database containing its
exact dependency closure, registered in deterministic dependency order. This
prevents concurrent registration in Cabal's shared database from changing GHC's
link-library order. The original databases remain the source of dependency
metadata and are never modified by this hook. Small application-only import
barriers order the executable helpers because GHC's `--make` linker retains
module compilation-completion order. Compiler libraries remain parallel.

Cabal 3.16 can report a package up to date after a Git-only change because its
outer cache does not monitor hook-only Git dependencies. The provenance hook
refreshes when the driver is rebuilt; this limitation is not addressed by
salting every library's build configuration with the repository revision.
Existing `.ba` version validation and language-visible version constants/macros retain
their original behavior until their compatibility policy is changed explicitly.
