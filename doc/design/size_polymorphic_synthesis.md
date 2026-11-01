# Size-polymorphic synthesis boundaries and a Bluespec-native primitive library

Status: proposal / implementation plan. Written against this fork at
`99677cb` (branch `claude/size-polymorphic-verilog-qhy2o1`). All paths are
relative to the repository root; `file:line` references were checked against
that revision.

## 0. Summary

Goal: Bluesim should stop implementing primitives in C++. Every primitive that
can be written in Bluespec gets a reference Bluespec implementation that all
backends (Verilog, Bluesim, the formal paths that read `.ba`) consume, and the
Verilog library (`src/Verilog/*.v`) and Bluesim runtime (`src/bluesim/
bs_prim_mod_*.h`) shrink to an irreducible core. The one thing standing in the
way is that a `synthesize` boundary must be monomorphic
(`src/comp/GenWrap.hs:424-438`), so a polymorphic `mkFIFO2 :: (Bits a sa) =>
Module (FIFO a)` cannot be a separate module the way `FIFO2.v` with
`parameter width` is.

Recommendation, in one sentence: do not try to emit Verilog with
`parameter width`; instead let `synthesize` on a polymorphic module mean
"synthesize one monomorphic module per distinct instantiation, named from the
type arguments" (C++-template style), driven on demand from the parent's
elaboration. The Verilog backend, the Bluesim backend and the `.ba` link flow
already work on exactly this shape; the only new machinery is a small hook in
the evaluator plus a worklist around the per-module driver loop in
`src/comp/bsc.hs`. Reference implementations are then ordinary Bluespec
modules whose port-level interfaces carry the existing port-naming
attributes, so the generated `FIFO2_32` has the same ports, parameters,
internal register names and warnings as `FIFO2 #(.width(32))`.

The plan has six phases. Phase 0 is a no-compiler-change prototype that
validates the fidelity targets. Phase 1 is the compiler feature. Phases 2 to 4
replace the FIFO family, the register-like primitives, and the synchronizers.
Phase 5 removes Bluesim code. Section 7 lists follow-on work (schedule
pinning, memory-file loading, parameterized shells).

## 1. What the compiler does today

### 1.1 The monomorphism gate is in GenWrap, and nothing downstream needs it relaxed in a deep way

* `genWrapE` runs before type checking (`src/comp/bsc.hs:386-436`). For each
  def carrying `PPverilog` it calls `chkType`, which rejects any remaining
  proviso ("It has a proviso.") and any free type variable ("Its interface is
  polymorphic.") (`src/comp/GenWrap.hs:424-438`; error text
  `src/comp/Error.hs:2232`). The only proviso it tolerates is `IsModule`,
  which `fixupPolyModType` ties to `Module` (`src/comp/GenWrap.hs:583-600`).
* The data structures already anticipate this feature and say so:
  `IfcTRec.rec_numargs`/`rec_typemap` carry the comment "Until we support
  synthesis of size-parameterized modules, the argument list and type map will
  be empty for synthesized modules" (`src/comp/GenWrap.hs:170-187`);
  `imod_type_args` is "always empty" (`src/comp/ISyntax.hs:156-159`);
  `iks = []` "this was to allow code-gen of modules with numeric parameters,
  but we don't support that" (`src/comp/IExpand.hs:816-818`);
  `aspkg_parameters`: "XXX there are no size parameters because we don't
  support synthesis of size-polymorphic modules" (`src/comp/ASyntax.hs:258`).
* GenWrap produces, per synthesized `mkFoo`: a flattened interface, an inner
  def `mkFoo<soft-hyphen>` of type `Module Foo_` (`src/comp/GenWrap.hs:
  1314-1451`), and a continuation `deffun` that, after the backend has run,
  builds the user-facing wrapper as a `CmoduleVerilog` import of the generated
  module (`src/comp/GenWrap.hs:1463-1536`, `src/comp/CSyntax.hs:573-612`).
  The wrapper is typechecked and spliced over the original def by
  `compileCDefToIDef`/`updDef` (`src/comp/bsc.hs:2314-2345`,
  `src/comp/FixupDefs.hs:222-257`), and that is what importers see: a
  foreign module with a `VModInfo` (`src/comp/IConv.hs:580-607`).

### 1.2 Everything needed to instantiate a child by a computed name already exists

* The Verilog module name of a `module verilog` / `import "BVI"` is a
  String-typed *expression*, evaluated at elaboration: `handlePrim` calls
  `evalString name` and sets `vName` (`src/comp/IExpand.hs:1693-1724`;
  parser rule `src/comp/Parser/Classic/CParser.hs:131`). The library already
  uses this to pick a module per size: `SPSRAM.bs` builds
  `"RRSPSRAM_" +++ nwords +++ "_" +++ valueOf dtas +++ "_bussed"`
  (`src/Libraries/Base2/SPSRAM.bs:72-76`).
* The backend instantiates whatever `vName` says and nothing else
  (`src/comp/AVerilogUtil.hs:1115-1120`). Verilog parameters on the instance
  come from `Param` args (`src/comp/AVerilogUtil.hs:1088-1097`); the
  synthesized module's own `parameter` declarations come from `param`
  module arguments (`src/comp/IExpand.hs:1084-1118`, `src/comp/AVerilog.hs:
  445-460`), and this fork already supports `Integer`-typed parameters
  (commit `e246d69`; `src/comp/IExpandUtils.hs:400-401`;
  `testsuite/bsc.verilog/parameters/integer/`). A parent parameter can be
  passed down to a child parameter (`src/comp/AVerilog.hs:1234-1240`).
* Per-width monomorphization by name mangling is already a pattern in this
  fork: polymorphic DPI functions become `f_w32_w8` per distinct width set
  (`src/comp/ForeignFunctions.hs:555-587`, `src/comp/AVerilogUtil.hs:
  1237-1241`), generated after Verilog emission because "the set of concrete
  widths is only known from the generated Verilog" (`src/comp/bsc.hs:
  1248-1257`). Classic `foreign` functions pass numeric type variables as
  named instance parameters (`fTyVarNames`, `src/comp/AConv.hs:548-565`,
  `src/Libraries/Base1/Fork.bs:18` against `src/Verilog/Fork.v:7-10`).
* Imported polymorphic module bodies are available to a downstream compile:
  the `.bo` stores every `IDef` with its full body (`src/comp/GenBin.hs:
  536-579`), `fixupDefs` re-ties `ICDef` pointers across packages
  (`src/comp/FixupDefs.hs:179-215`), and `evalAp'` on `ICon i (ICDef t e)`
  evaluates the imported body in place (`src/comp/IExpand.hs:3365-3376`).
  Type application is beta-reduction of `ILAM` (`src/comp/IExpand.hs:3399`),
  so the concrete type arguments are visible at exactly one point.
* Package pragmas (including `Pproperties i [PPverilog]`) are serialized
  into the `.bo` (`src/comp/GenBin.hs:541`), so a "this module is
  specializable" marker survives to importers.

### 1.3 Why true parameterized Verilog is not the minimum

* `type ASize = Integer` (`src/comp/ASyntax.hs:520`); every size in
  ASyntax, every literal width (`src/comp/IntLit.hs:14-16`), every
  `.ba` (`src/comp/BinData.hs:1017-1027`) and Bluesim's `aTypeToCType`
  (`src/comp/SimCCBlock.hs:366-372`) assume a literal. `PrimValueOf` on a
  non-`ITNum` is an internal error (`src/comp/IExpand.hs:3952`);
  `chkStateVarTypes` rejects free type variables in state (`src/comp/
  IExpand.hs:1866-1895`).
* Width-dependent rewrites are everywhere: AOpt masks and extract bounds
  (`src/comp/AOpt.hs:584, 847-878, 1398-1464`), AVeriQuirks sign extension
  (`src/comp/AVeriQuirks.hs:207-237`), the SAT disjointness tests in
  scheduling that need concrete bit-vector sorts (`src/comp/AExpr2STP.hs:
  424-512`), zero-width port elision at a dozen sites (`src/comp/AVerilog.hs:
  171-172, 390`, `src/comp/AVerilogUtil.hs:975-1069`).
* The only symbolic widths bsc emits today are the hand-built `Mux_n`
  primitives (`src/comp/VPrims.hs:21-34`), which shows the Verilog AST can
  print them (`type VRange = (VExpr, VExpr)`, `src/comp/Verilog.hs:804`)
  but nothing upstream of AVerilog can produce them.
* For a FIFO the data registers *are* the parameter, so there is no
  "restricted class" of modules whose body stays width-concrete.
* The evaluator itself is a concrete-width partial evaluator: `doPrimOp`
  binds result widths from `[i | ITNum i <- ts]` (`src/comp/IPrims.hs:
  26-37`), the strict-primitive folding path passes only `ITNum` type args
  (`src/comp/IExpand.hs:4337-4364`), and `IntLit` carries a concrete
  `ilWidth`. The one place a payload is treated opaquely is the fork's lazy
  pack/unpack (`ICLazyPack`/`ICLazyUnpack`, `src/comp/IExpand.hs:
  4019-4062`), which is what lets a reference FIFO body stay agnostic of the
  payload *type* while its *width* is still concrete.

### 1.4 Bluesim needs nothing but monomorphic `.ba` modules with unique names

* Bluesim treats any `AVInst` whose name is in `primMap` as a C++ template
  class and everything else as a synthesized submodule whose `.ba` it finds
  by module name on the `-p` path (`src/comp/SimPrimitiveModules.hs:
  263-355`, `src/comp/ABinUtil.hs:234-418`). One C++ class per module type
  (`src/comp/SimMakeCBlocks.hs:72-114`, `src/comp/SimCCBlock.hs:1692`),
  schedules flattened into the parent (`src/comp/SimExpand.hs:758-1112`).
* Hierarchy is kept for VCD scopes and Bluetcl `sim cd/ls/lookup`
  (`src/comp/SimCCBlock.hs:1986-1997`, `src/comp/bluetcl.hs:2656-2722`),
  which is why boundaries, not just inlining, matter for waveform fidelity.
* The C++ primitives mimic the Verilog port names in their VCD scopes
  (`FULL_N, EMPTY_N, ENQ, D_IN, DEQ, CLR, D_OUT`, `src/bluesim/
  bs_prim_mod_fifo.h:263-293`) but not the internal names (`arr_0` vs
  `data0_reg` in `src/Verilog/FIFO2.v:51-54`). A reference implementation
  compiled by both backends removes that divergence.
* Bluesim `$display` supports `%m` (`src/bluesim/dollar_display.cxx:949`),
  so the Verilog-style warnings can be reproduced verbatim.

### 1.5 Formal backends see boundaries as opaque constructors

The LambdaCalc/SAL paths run once per synthesized module inside `genModule`
(`src/comp/bsc.hs:854-860`) with no link step. They have their own
name-keyed primitive table "similar to the one in SimPrimitiveModules"
(`src/comp/LambdaCalcUtil.hs:1247-1296`), and any non-primitive submodule
is emitted as an opaque constructor call named by `vName`
(`src/comp/LambdaCalc.hs:682-686, 721-722`) with the comment "synthesized
user modules are not polymorphic". Two consequences for this plan:

* A per-size reference module is a separately dumped unit for formal, which
  is what compositional work wants (prove `FIFO2_32` against `FIFO2
  #(.width(32))` once, then treat it as a black box), but the MatX formal
  flow must compose those dumps itself; bsc will not inline them. A design
  that wants the reference *inlined* into the module under analysis uses the
  un-synthesized reference module (any polymorphic module instantiates
  inline when it is not marked `synthesize`), which is the same source.
* LambdaCalcUtil's table, like Bluesim's, matches by Verilog name, so a
  reference module must not reuse a primitive's exact name while the table
  still lists it (see risk 7 in section 8).

### 1.6 Upstream context

* The BSV reference guide states the limitation and its cause: "Since the
  bsc compiler does not create 'parameterized' Verilog, in order for a module
  to be synthesizable, the associated interface must be fully specified"
  (`doc/BSV_ref_guide/BSV_lang.tex:3216-3219`), documents the per-type
  alias workaround (`BSV_lang.tex:3125-3131`), and says of `parameter`
  arguments that "structural decisions (generate decisions) are taken by the
  compiler bsc, and cannot currently be postponed into the Verilog"
  (`BSV_lang.tex:2178-2185`). The bluetcl chapter documents the
  `InstSynth.tcl` typeclass workflow (`MakeInst_<module>`,
  `doc/user_guide/bluetcl.tex:876-980`) that this plan makes unnecessary.
* B-Lang-org/bsc issue #543 (2023) asks for width-as-Verilog-parameter;
  quark17's reply lists the obstacles (overloaded operations, conditional
  instantiation on `valueOf`, fully unrolled loops) and floats
  `(* synthesize *)` on an instantiation. Issue #921 (nanavati, 2026-04,
  "allow synthesize pragmas on instantiations") is this proposal's closest
  relative: quark17's comment there says "I had always assumed that we'd
  implement submodule synthesis by discovering them during elaboration: BSC
  would elaborate until it found such a submodule, then would have to stop
  and elaborate the submodule ... and then come back", and names three
  levels (concrete type at typecheck; pragma inside a polymorphic parent;
  non-synthesizable arguments such as `Integer` known only at elaboration).
  Section 3 covers all three with one mechanism, and 3.2 is the third level.
* Issue #824 wants `mkPipelineFIFO`/`mkBypassFIFO` visible as modules in
  VCDs ("if we had synthesis for polymorphic modules, then I could just
  synthesize it once"); they become ordinary candidates for `synthesize`
  under this plan. Issue #1063's `WrapInterface` idea (replace GenWrap by a
  typeclass) is compatible: 3.6 only needs *a* wrapper generator for a
  monomorphic alias, whichever implementation produces it.
* Merged upstream precedents this fork already carries: `WrapField`/
  `SplitPorts` (PR #729), named foreign instance parameters (PRs #1022,
  #1023), Integer module parameters (PR #1034 = local `e246d69`), DPI
  monomorphization (PR #999). The error `ENotKNum` "Only size polymorphism
  allowed in code generation" (`src/comp/Error.hs:2228`) is defined but
  never raised, a vestige of an earlier attempt in the same direction.

## 2. Options considered

| Option | What changes | Verdict |
|---|---|---|
| A. Demand-driven monomorphic specialization: `synthesize` on a polymorphic module generates `mkFoo_<args>` per distinct instantiation, from the parent's elaboration | GenWrap gate; one evaluator hook; worklist in the driver; naming; cross-package registry | **Chosen.** Reuses the whole existing pipeline; Bluesim and formal get real boundaries; names are stable and tool-friendly |
| B. Emit `parameter width` Verilog from one elaboration | Symbolic `ASize` through AConv, AState, AOpt, AVeriQuirks, ASchedule/SAT, AVerilog, BinData, Bluesim | Rejected for the minimum. Multi-month rewrite with loss of SAT on width-dependent logic; Bluesim still needs per-width classes |
| C. Library-only: explicit per-width aliases, `mkUCount`-style ladders, computed `module verilog` names plus a hand-maintained `-g` list or `InstSynth.tcl` (`util/bluetcl-scripts/InstSynth.tcl`) | No compiler change | Useful as the Phase 0 prototype only. Does not scale, the alias list must be maintained by hand per design, the computed-name import is Classic-only (BSV `import "BVI"` takes an identifier, `src/comp/Parser/BSV/CVParser.lhs:4645-4654`), and nothing checks a hand-written BVI schedule against the module it names |
| D. Witness elaboration: elaborate at two template widths, fit `a*n+b`, substitute a parameter name in AVerilog | AVerilog-only post-pass | Fragile (AOpt folds differ by width, zero-width elision). Possible follow-on for a parameterized *shell* around A's output, see 7.3 |

Why A is the minimum: every piece except the hook and the worklist exists
(1.2). It is also what Bluesim already does for primitives: `MOD_Reg<tUInt32>`
and `MOD_Reg<tUInt8>` are two classes. The cost is one extra Verilog file per
distinct instantiation and a module name that carries the type arguments
(`FIFO2_32` rather than `FIFO2 #(.width(32))`), which downstream scripts
keyed on primitive names must tolerate (a `_<n>` suffix regex).

## 3. Phase 1: demand-driven specialization in the compiler

### 3.1 Semantics

A module def marked `synthesize` (`{-# verilog mkFoo #-}` in Classic,
`(* synthesize *)` in BSV, or `-g mkFoo`) whose context-reduced type still
has type variables, provisos, or *static arguments* (3.2) is **specializable**.
No Verilog is produced when its own package is compiled. Each instantiation
at concrete type arguments and static argument values, in any later
elaboration (same package or an importer), produces one monomorphic
synthesized module named from those arguments (3.5), and the parent
instantiates that module as a submodule. Identical (def, type args, static
args) anywhere in the design map to the same module name and are generated
once per compile and reused across packages (3.6).

Everything else about a synthesized module is unchanged: `param` arguments
become Verilog parameters, `Bits` arguments become ports, clocks and resets
become ports, port-naming attributes apply, `.ba` is written in `-sim` and
`-elab` modes.

Definition-site versus instantiation-site marking. Issue #921 proposes a
pragma on the *instantiation* (`(* synthesize *) let f <- mkFIFO;`). The
primitive library needs the *definition-site* form: every instantiation of
the reference `mkFIFO2`, by any user, must get a boundary without the user
annotating it, and the Bluesim primitive table is keyed by the module, not
by call sites. The two forms share the mechanism below (the instantiation
form is the same hook, triggered by a pragma on the `PrimModuleBind` instead
of by the def's marker) and the instantiation form is a natural second step
once the definition form is in.

### 3.2 Static arguments

Today an `Integer`, `String` or `Real` module argument on a synthesis
boundary must be marked `parameter`, else `EParamOnlyType` (`src/comp/
IExpand.hs:1100-1101`, `src/comp/Error.hs:4027`). For specializable modules
the new rule is: such an argument *without* `parameter` is a **static
argument**: it is part of the specialization key, must evaluate to a constant
at the instantiation, and is mangled into the module name. This is what
`SizedFIFO`'s `depth` needs (it sizes storage, which a Verilog parameter
cannot do, `doc/BSV_ref_guide/BSV_lang.tex:2177-2181`), and it is the same
distinction the library already makes between `p2depth` (structural) and
`guarded` (value) in `src/Libraries/Base1/FIFOF_.bsv:235-240`. With
`parameter`, the existing fork behavior (a real Verilog parameter) is kept.

### 3.3 GenWrap changes (`src/comp/GenWrap.hs`)

1. In `getDef`/`chkType`: when `generating` and the def has `PPverilog` but
   fails the monomorphism checks for reasons that type arguments can fix
   (free type variables, provisos other than `IsModule`, static arguments),
   do not error and do not create a `WrapInfo`. Instead mark the def as
   specializable: add `PPspecialize` to its `Pproperties` (new `PProp`
   constructor in `src/comp/Pragma.hs`, printed as `specialize`), and leave
   the def body untouched (no `fixDef` placeholder). Keep erroring when the
   *interface* cannot be made monomorphic by any instantiation (polymorphic
   fields, `isPolyFieldType`, non-interface result, non-module) so the
   message surfaces at the definition.
2. Keep `fixupPolyModType` as is; the alias defs created in 3.4 have
   `Module` types and pass `chkType` unchanged.
3. `-g mkFoo` on a specializable module with no instantiation in the compile
   is an error with a new message: "`mkFoo` is size-polymorphic; it is
   synthesized per instantiation. Instantiate it from a synthesized module,
   or give a monomorphic alias." (new `ErrMsg` next to `EBadIfcType`).
4. New optional module pragma `verilog_name = "Name"` (`PPverilogName
   String`): GenWrap uses it instead of `getIdBaseString i` for the module
   name literal (`src/comp/GenWrap.hs:1525`) and AConv for `apkg_name`
   (`src/comp/AConv.hs:313`). This is what lets a Bluespec def `mkFIFO2`
   generate `FIFO2_32` rather than `mkFIFO2_32`, which downstream tooling
   keyed on the Verilog library names needs. Small, independent, and useful
   on its own.

### 3.4 The evaluator hook (`src/comp/IExpand.hs`)

Single hook point: `evalAp' (ICon i (ICDef t e)) as` (`src/comp/IExpand.hs:
3365-3376`), where `i` is the def and `as` the argument stack with type
arguments first (`ILAM`s precede `ILam`s, `src/comp/ISyntax.hs:445-448`),
then dictionary lambdas (binders with `isDictId`, `src/comp/Id.hs:532`),
then value arguments.

If `i` is specializable (looked up in a set built from `ipkg_pragmas` of the
current and all imported packages, `GState`):

1. Normalize the type arguments with `fullTypeNormalizer`
   (`src/comp/IExpandUtils.hs:2576-2611`); if any is not fully concrete,
   error (position of the application): "type arguments of specializable
   module `mkFoo` could not be determined". Evaluate each static argument to
   NF with the machinery used for submodule args (`iExpandSubmodArg`,
   `src/comp/IExpand.hs:2173-2185`); non-constant is an error (parallel to
   `EModParameterDynamic`, `src/comp/Params.hs:95-100`).
2. Compute the key `(qualified i, [IType], [static values])` and its
   mangled name (3.5).
3. **Redirect mode** (the normal mode): look the name up in the
   specialization registry (3.6). If present, replace the application by the
   registry's wrapper def applied to the *remaining* arguments (drop the type
   args, the dictionary args and the static args; keep ports, `param`s,
   clocks, resets, in order) and continue. The wrapper is an ordinary
   `Module` value whose body is an `ICVerilog` application, so `handlePrim`
   instantiates it like any synthesized submodule, including `clocked_by`/
   `reset_by`, instance naming through `IStateLoc`, and automatic
   `primSavePortType` entries.
4. **Miss**: record the key in a new `GOutput` field (`go_spec_demands`, next
   to `go_state_vars`, `src/comp/IExpandUtils.hs:674-688`) and fall through
   to the existing inline evaluation. The parent's elaboration completes as
   today (so the result is well-formed and all *other* demands are discovered
   in the same run); the driver discards it and re-runs once the demanded
   modules exist (3.6).
5. If the application is not saturated through its static prefix (type args
   plus dictionaries plus all static args), inline as today and emit a
   warning naming the def; this is the only case where a specializable
   module silently loses its boundary. (Module constructors are applied
   saturated at `PrimModuleBind` in practice, so this should not fire on
   library code.)

Bluesim, Verilog, `-elab`, LambdaCalc/SAL need no change: a specialized
module is a normal synthesized module with a `.ba` and a `.v`.

### 3.5 Naming

`mangle :: Id -> [IType] -> [static value] -> String`:

* base = `verilog_name` pragma if present, else the def's base name;
* each argument appended as `_<text>`: `ITNum n` → decimal; a `Bit n`,
  `UInt n`, `Int n` → `b<n>`/`u<n>`/`i<n>`; `Bool` → `Bool`; an `Integer`
  static → decimal (negative as `m<n>`); a `String` static → the string if
  it is a legal identifier fragment, else hashed; any other type (structs,
  `Maybe (Bit 7)`, vectors) → the printed type with non-identifier
  characters replaced by `_`;
* if the result exceeds 64 characters or any argument needed replacement, use
  `<base>__h<16-hex-digit hash of the canonical key>` instead, so names stay
  legal for Verilog, file systems and C++ identifiers (`MOD_<name>`).

Library reference modules take only numeric type parameters (like `VReg n`,
`src/Libraries/Base1/Prelude.bs:1989`), so they always get the readable form:
`FIFO2_32`, `FIFO2_0`, `SizedFIFO_32_16`, `Counter_8`, `CReg_32_3`.

The hash form must be deterministic across packages and compiler runs: hash
the canonical `pfpString` of qualified id and types, not pointer identities.

The key is the full list of type arguments, not just the widths they
imply: a module polymorphic in `a` may inspect `a` through other classes
(`Eq`, `FShow`, `Arith`), so `Maybe (Bit 7)` and `Bit 8` are different
specializations even though both are 8 bits wide. Library cores avoid the
question by being polymorphic only in numeric types (`Bit n` payloads), and
the wrapper does the `pack`/`unpack`, which the fork's lazy pack/unpack
cancels at the boundary (`src/comp/IExpand.hs:4019-4062`).

### 3.6 Driver worklist (`src/comp/bsc.hs`)

Replace the fixed fold over `ordgens` (`src/comp/bsc.hs:566-660`) with a
worklist:

```
genAll items registry = for each item (a WrapInfo or a SpecRequest):
  (result, demands) <- genModule item (Redirect registry)
  if demands /= []:
     for d in demands not in registry: registry <- genSpec d registry
     (result, []) <- genModule item (Redirect registry)   -- must be clean now
  splice result (updDef) ; continue
```

`genSpec (i, tys, statics)`:

1. Build a monomorphic alias at CSyntax level: a `CDef` named by `mangle`,
   with the def's `CQType` scheme (from the symbol table, `findVar`) with
   type variables substituted by `iToCT` of the type args and the static
   argument positions removed, and a clause whose binders reuse the original
   `ILam` binder names (so `PPparam`, `port` and clock/reset pragmas keyed by
   argument name still apply) and whose body applies `mkFoo` to literals for
   the static arguments and to the binders for the rest. Copy `mkFoo`'s
   module-level pragmas (`PPCLK`, `PPRSTN`, `PPGATE`, always-ready/enabled,
   `PPparam`, `verilog_name`) to the alias, replacing `PPspecialize` by
   nothing and keeping `PPverilog`.
2. Run the single-def GenWrap path on a synthetic `CPackage` holding that
   def and pragma with the current symbol table (`genWrapE`), then the
   standard deriving / context reduction / typecheck / `iConv` on the
   generated defs (flattened ifc, `to_`/`from_`, inner def), merge the
   resulting `IDef`s into the current `IPackage`, run `fixupDefs`. The
   `noinline` machinery is the precedent for fabricating defs this way
   (`src/comp/GenFuncWrap.hs:112-199`); `compileCDefToIDef`
   (`src/comp/bsc.hs:2314-2345`) is the precedent for typechecking one def
   late.
3. Recursively `genAll` the inner def (its own demands are grandchildren),
   then run its `deffun` to get the wrapper `CDef`, `compileCDefToIDef` it,
   add the wrapper `IDef` to the package with a new id property
   `IdPSpecialization` and insert it into the registry.
4. Guard recursion: a depth limit (64) and detection of a key demanding
   itself; both are errors naming the chain.

Registry: `Map String IDef` seeded from every imported package's defs tagged
`IdPSpecialization` (they are ordinary exported defs in the `.bo`, hidden
from the user signature like `IdPGeneratedIfc` defs, `src/comp/GenSign.hs:
544`) plus what this compile generates. Two independent packages that both
need `FIFO2_32` each write `FIFO2_32.v`/`.ba`; link-time hierarchy walk
dedupes by name (`src/comp/ABinUtil.hs:226-227`). Store the compile flags
fingerprint already carried in `ABinModInfo` and warn at link when two `.ba`
of the same name disagree. (Today `.ba` hashing is disabled,
`src/comp/GenABin.hs:46-51`, so this is advisory.)

Outputs: `.v` to `-vdir`, `.ba` to `-bdir` exactly as for other synthesized
modules (`src/comp/bsc.hs:1283-1300, 1032`). `Depend.hs` cannot predict
specialization outputs; treat them like the DPI wrappers (`src/comp/
Depend.hs:230-241`): regenerated whenever the generating package compiles.

Cost: a parent that discovers at least one new specialization is elaborated
twice. Second and later compiles of the same package, and all packages whose
demands are already in imported registries, elaborate once. Two ways to
avoid the second elaboration, neither needed for the first version:

* **Static pre-scan.** After IConv, `IAps` nodes carry explicit type
  arguments (`src/comp/ISyntax.hs:446`) and numeric type functions are
  already folded when their arguments are literals (`src/comp/IType.hs:
  458-473`). A scan of the parent's `IDef` for applications of specializable
  ids with all-literal type arguments and literal static arguments finds
  most library demands (a monomorphic parent instantiating `mkFIFO2` at
  `Bit 32`) before elaboration; the hook then only catches demands that
  depend on elaboration (polymorphic parents, sizes computed from `Integer`
  arguments, loops).
* **Re-entrant child compile.** `G` is `StateT GState IO` with a fresh
  `GState` per `runG` and no global mutable state beyond per-heap `IORef`s
  (`src/comp/IExpandUtils.hs:492, 690-696`), so the hook could `lift` a
  nested `genModule` for the child and continue the parent with the real
  wrapper in hand. This is the "stop, elaborate the submodule, come back"
  design quark17 describes in issue #921.

### 3.7 Flags and compatibility

* Gate the feature behind `-specialize-synth` (default on after the library
  switch in Phase 2; off restores today's error). Behavior for monomorphic
  modules is unchanged either way.
* `-g Pkg.mkFoo` on a specializable module: error (3.3.3).
* `showrules`, `bluetcl` module listings and `-show-schedule` see specialized
  modules as ordinary modules named by `mangle`.

### 3.8 Tests (`testsuite/bsc.synthesize/specialize/`)

* `PolyIfc.bs`: `mkQueue :: (Bits a sa) => Module (Q a)` marked
  `synthesize`, instantiated at `Bit 8` and `Bit 32` in one parent: expect
  `mkQueue_b8.v`, `mkQueue_b32.v`, parent instantiates both by name, no
  `parameter width`.
* Static argument: `mkArr :: Integer -> Module (A n)` at `(8, 4)` and
  `(8, 7)`: `mkArr_8_4`, `mkArr_8_7`; dynamic static argument is an error.
* `param` argument alongside: `parameter guarded` in the specialized module,
  `.guarded(1'd1)` at the instantiation.
* Zero width: `Bit 0` instantiation elides the data ports.
* Nested: specializable module instantiating a specializable module.
* Cross-package: `A.bs` defines, `B.bs` and `C.bs` both use the same width;
  one generation when `C` imports `B`, two identical files when it does not.
* `verilog_name`: def `mkFIFO2` produces `FIFO2_32`.
* Bluesim: `test_c_veri_bsv_multi` on each design; VCD scope names via the
  `vcd_correlation` harness (`testsuite/bsc.bluetcl/vcd_correlation/`).
* Errors: `-g` on a specializable module; unresolved type argument;
  recursion limit; the existing `noinline` polymorphic error still fires
  (`testsuite/bsc.verilog/noinline/NoInline_Polymorphic.bsv`).

Estimated size: 800 to 1200 lines of Haskell plus tests, concentrated in
`GenWrap.hs`, `IExpand.hs`/`IExpandUtils.hs`, `bsc.hs`, `Pragma.hs`,
`Error.hs`, `Id.hs`.

## 4. Phase 0 and Phase 2: the FIFO family as the pilot

### 4.1 Shape of a reference primitive

Keep the library's existing two layers (`src/Libraries/Base1/FIFOF_.bsv`
primitive imports, `src/Libraries/Base1/FIFOF.bs` guards) and replace only
the primitive layer. The reference core has the *port-level* interface of
the Verilog module: unguarded methods, one method per port group, port names
fixed by attributes. In Classic (the Prelude dialect):

```
interface VFIFO2 n =
    enq     :: Bit n -> PrimAction {-# always_ready, prefix = "", arg_names = [D_IN], enable = "ENQ" #-}
    deq     :: PrimAction          {-# always_ready, enable = "DEQ" #-}
    first   :: Bit n               {-# always_ready, result = "D_OUT" #-}
    full_n  :: Bool                {-# always_ready, result = "FULL_N" #-}
    empty_n :: Bool                {-# always_ready, result = "EMPTY_N" #-}
    clear   :: PrimAction          {-# always_ready, enable = "CLR" #-}

-- Classic module pragmas take the brace form parsed by pVeriGenProps
-- (src/comp/Parser/Classic/CParser.hs:635-660); verilog_name is new (3.3.4)
{-# verilog mkFIFO2 { parameter guarded, reset_prefix = "RST", verilog_name = "FIFO2" } #-}
mkFIFO2 :: Bool -> Module (VFIFO2 n)
mkFIFO2 guarded = module
    full_reg  :: Reg Bool <- mkReg True      -- active-low full, as FIFO2.v
    empty_reg :: Reg Bool <- mkReg False
    data0_reg :: Reg (Bit n) <- mkRegU
    data1_reg :: Reg (Bit n) <- mkRegU
    enq_w :: RWire (Bit n) <- mkRWire
    deq_w :: RWire () <- mkRWire            -- PulseWire lives in PreludeBSV, which Prelude.bs cannot import
    clr_w :: RWire () <- mkRWire
    rules ... -- transliteration of FIFO2.v:63-66, 92-121
    ... warning rule: when guarded, $display "Warning: FIFO2: %m -- Enqueuing to a full fifo"
    interface ...
```

The attribute set used here is the one documented in
`doc/BSV_ref_guide/BSV_lang.tex:9320-9420` (`ready`, `enable`, `result`,
`prefix`, `port`; Classic spelling `arg_names`, see `src/comp/Pragma.hs:
748-756` and the example in `src/Libraries/Base1/GetPut.bs:116`), plus
`reset_prefix` (`src/comp/Pragma.hs:118-120`) and the new `verilog_name`.
The default reset port is `RST_N` (`src/comp/FlagsDecode.hs:685`); the
primitive library uses `RST` with polarity from `BSV_POSITIVE_RESET`, and
generated Verilog uses the same macros (`src/comp/Verilog.hs:111-116`,
`src/comp/InlineReg.hs:208`), so only the name needs setting.

Expected header of the specialization at 32 bits:

```
module FIFO2_32(CLK, RST, D_IN, ENQ, DEQ, CLR, D_OUT, FULL_N, EMPTY_N);
  parameter guarded = 1'd0;      // default differs from FIFO2.v (1'b1), see 4.3
  input  CLK; input RST;
  input  [31 : 0] D_IN; input ENQ; input DEQ; input CLR;
  output [31 : 0] D_OUT; output FULL_N; output EMPTY_N;
  reg full_reg; reg empty_reg; reg [31 : 0] data0_reg; reg [31 : 0] data1_reg;
  ...
```

The outer `vMk2FIFOF` import in `FIFOF_.bsv:142-167` becomes a Bluespec
wrapper over `mkFIFO2` that reproduces `FIFOF_` (`notFull`/`i_notFull` both
read `full_n`), and the `valueOf(sa)==0` branch (`FIFOF_.bsv:193-220`) goes
away because `FIFO2_0` elides its data ports. The wrapper keeps calling
`primSavePortType` with the unpacked source type for `D_IN`/`D_OUT`, as
`mkReg` does (`src/Libraries/Base1/Prelude.bs:2025-2028`), so waveform and
`wiretypemap` consumers see `Maybe (Bit 7)` rather than `Bit 8`.

### 4.2 Phase 0: validate without compiler changes

Before any compiler work, prove the fidelity targets with monomorphic
aliases, which already synthesize today:

1. Write `mkFIFO2` as above in a scratch package; add
   `{-# verilog mkFIFO2_32 #-} mkFIFO2_32 :: Bool -> Module (VFIFO2 32);
   mkFIFO2_32 = mkFIFO2` for widths 1, 32, 0 (and the same for FIFO1,
   FIFOL1, FIFOL2, SizedFIFO at two depths).
2. Diff the generated port list and parameter list against the `.v` files.
3. Lockstep equivalence: a Verilator testbench that drives `FIFO2 #(32)` and
   `FIFO2_32` with the same random `ENQ/DEQ/CLR/D_IN` stream including
   illegal uses (enq when full, deq when empty, simultaneous enq/deq when
   full, `FIFO2.v:63`) and compares `FULL_N/EMPTY_N/D_OUT` every cycle; and,
   where available, a formal equivalence check (Yosys `equiv_*` or SymbiYosys)
   per width. This is the "useful for formal work" payoff and becomes a
   permanent test.
4. Bluesim/Verilog co-simulation of a design using the wrapper
   (`test_c_veri_bsv_multi`), and a VCD comparison of the `FIFO2` scope
   between Bluesim and Verilog (today the harness only checks that dumping
   does not change behavior, `testsuite/config/unix.exp:3235-3330`; add a
   name-set comparison).
5. `-show-schedule` diff on the existing FIFO tests (`testsuite/bsc.lib/
   fifo`) to see which user-visible annotations change (4.3).

Exit criteria: identical port/parameter names, identical register names,
cycle-exact behavior under legal and illegal use, identical warning text.

### 4.3 Fidelity checklist and known deltas

| Item | Status with this plan |
|---|---|
| Port names and widths | Identical via attributes; zero-width ports elided automatically (`src/comp/AVerilog.hs:171-172`) |
| Port order in the header | Differs (bsc groups by method). bsc uses named connections; only positional external instantiations notice |
| Parameters | `guarded`, `init`, etc. identical names via `parameter` args. Generated defaults are 0 (`src/comp/AVerilog.hs:453`, "XXX parameters are always given the default value of 0"); fix in AVerilog by taking the default from a `default` pragma or leave, since bsc always passes explicit values |
| `width` parameter | Absent; the width is in the module name. Optional: an unused `parameter width` via an `Integer` `parameter` argument fed `valueOf n`, for scripts that read it |
| Module name | `FIFO2_32` instead of `FIFO2`. Downstream name lists need a `_\d+` suffix allowance. `FIFO20` becomes `FIFO2_0` |
| Clock and reset names | `CLK` default; `RST` via `reset_prefix`; polarity macros identical |
| Internal registers | Named as in the `.v` (`full_reg`, `empty_reg`, `data0_reg`, `data1_reg`); inlined as `reg` with `$D_IN`/`$EN` wires (`src/comp/InlineReg.hs`), extra vs the hand-written `d0di`/`d0h` wires |
| Rule signals | `CAN_FIRE_RL_*`/`WILL_FIRE_RL_*` appear (with `-keep-fires`) and in Bluesim VCDs; new signals, no clash |
| `initial` blocks | Same `0xAA` pattern under `BSV_NO_INITIAL_BLOCKS` |
| Warnings | Same text via `$display` with `%m`; emitted from a rule under `guarded` and the `(!DEQ \|\| guarded)` condition (`FIFO2.v:132-147`) |
| Reset style macros | `BSV_ASYNC_RESET`, `BSV_RESET_FIFO_HEAD`, `BSV_RESET_FIFO_ARRAY` are Verilog-compile-time switches with no bsc analogue. Decide per MatX flow; if needed, a bsc flag selects `mkRegA` and reset-on-data inside the cores |
| Schedule annotations | Derived instead of asserted. Expect `first CF deq` where the BVI said `first SB deq`, and `clear CF enq/deq` where it said `SBR`; these are relaxations with the same hardware meaning, but can change rule conflicts in existing designs. See 7.1 for pinning |
| Path info | Derived; loopy FIFOs get `path (DEQ, FULL_N)` automatically because `full_n` reads `deq_w` |
| Port type info | GenWrap records `Bit n`; the wrapper overrides with the source type as `mkReg` does |
| Bluesim VCD | Module scope with ports and the four registers (today: ports plus `arr_0`, `arr_1`); matches Verilog instead of the C++ model |
| Bluetcl `sim` symbols | Registers and rules instead of the hand-coded `depth`/`level` symbols (`src/bluesim/bs_prim_mod_fifo.h:58-76`) |
| Bluesim speed | Each FIFO becomes a module with rules in the flat schedule rather than a C++ method call; measure on a FIFO-heavy design before Phase 5 removes the C++ |

### 4.4 Phase 2 deliverables

1. `src/Libraries/Base1/FIFO_Ref.bs` (or inside `FIFOF_.bsv`): `mkFIFO1`,
   `mkFIFO2`, `mkFIFOL1`, `mkFIFOL2`, `mkSizedFIFO` (depth static,
   registered head and ring as in `src/Verilog/SizedFIFO.v:65-67, 180`),
   `mkSizedFIFOL`, each with `verilog_name` equal to the `.v` name.
2. `FIFOF_.bsv`: `vMk1FIFOF`, `vMk2FIFOF`, `vMkSizedNFIFOF`, loopy variants
   and their `0` variants become wrappers over the cores; keep the BVI
   imports under `*_BVI` names for one release behind
   `-no-specialize-synth` so existing flows can A/B.
3. `src/Verilog/FIFO*.v`, `SizedFIFO*.v` stay in the tree for external users
   and for the equivalence tests; they are no longer referenced by the
   library.
4. Tests from 4.2 become permanent; regold `testsuite/bsc.lib/fifo` and any
   `-show-schedule` goldens that change, after review of each change.

## 5. Phases 3 and 4: the rest of the primitive map

Classification of every `primMap` entry (`src/comp/SimPrimitiveModules.hs:
263-348`), with the Bluespec building blocks a reference would use.

### 5.1 Core: stays native in both backends

| Primitive | Why it stays |
|---|---|
| `RegN`, `RegUN`, `RegA` | The state element |
| `ConfigRegN/UN/A` | Differs from `RegN` only by the `read CF write` annotation, which cannot be *derived* from a body (deriving gives `read SB write`); keep until schedule pinning (7.1) can express an intentional relaxation |
| `RWire`, `RWire0`, `BypassWire`, `BypassWire0` | The intra-cycle communication primitive |
| `CrossingRegN/UN/A`, `CrossingBypassWire`/`BypassCrossingWire`, `LatchCrossingReg`, `RegAligned` | The sanctioned unsafe clock-domain read; everything in Phase 4 is built on these |
| `ClockGen`, `MakeClock`, `GatedClock`, `ClockInverter`, `GatedClockInverter`, `ClockDiv`, `GatedClockDiv`, `ClockSelect`, `UngatedClockSelect`, `ClockMux`, `UngatedClockMux` | Create or alter clocks; coupled to `bk_alter_clock`/`bk_trigger_clock_edge` (`src/bluesim/bs_prim_mod_clockgen.h:80`) |
| `MakeReset[A/0]`, `SyncReset[A/0]`, `InitialReset`, `ResetMux`, `ResetEither`, `ResetToBool` | Reset is a side channel, not a value (`src/comp/SimCCBlock.hs:1650-1659`) |
| `RegFile`, `RegFileLoad`, `BRAM*Load`, `DualPortRam` storage | A dense memory array. Functionally a `Vector n (Reg a)` is a reference implementation and is fine for formal, but a 64K-entry BRAM as 64K `MOD_Reg` objects is unusable in Bluesim, and the `Load` variants need `$readmemh` (`src/bluesim/bs_prim_mod_regfile.h:284`). Keep one "memory array" core primitive (RegFile semantics: 5 async reads, 1 sync write, optional file load); build BRAM behavior on it (5.3). See 7.2 |
| `Probe`, `ProbeWire` | Sinks with keep semantics; `Probe` has no `.v` and is dropped by AVerilog (`src/comp/AVerilog.hs:1913`). Could become an empty boundary module later |
| System tasks (`$display`, `$finish`, `$time`, plusargs, `$dumpvars`) | Runtime services, not modules |

### 5.2 Phase 3: register-like primitives (Bluespec over Reg + RWire)

| Primitive | Reference | Fidelity notes |
|---|---|---|
| `Counter` (`src/Libraries/Base1/Counter.bs:24, 65`, `Cntrs.bsv:62`) | `mkReg init` plus RWires for `ADDA/ADDB/SETC/SETF`, one rule with the priority of `src/Verilog/Counter.v:59-62` | `init` as `parameter`; the BVI's "a lie!" annotation (`Counter.bs:35`) becomes derived and honest |
| `RegTwoN/UN/A` (`src/Libraries/Base2/RegTwo.bs`) | Reg plus two write RWires with the `.v` priority | straightforward |
| `RevertReg` (`src/Libraries/Base1/RevertingVirtualReg.bs:9`) | `_read = init`, `_write` writes `init` into a real `mkReg` so `read SB write` is derived (the purpose of the module is the ordering constraint); the flop is constant and synthesis removes it | `RevertReg.v` has no flop (`src/Verilog/RevertReg.v:17`); Bluesim maps it to a Reg already |
| `McpRegUN` (`src/Libraries/Base2/Mcp.bs:417`) | shift register of `delay` (static) stages | `delay` becomes a static argument |
| `CRegN5/UN5/A5` (`src/Libraries/Base1/PreludeBSV.bsv:692-800`) | one `mkReg` plus `n` RWires and the chained mux of `src/Verilog/CRegN5.v:79-90`; make `n` a static argument so `CReg_32_3` has exactly three ports instead of five | Two consequences to decide: (a) in Verilog today CRegs are *inlined* into the parent (`src/comp/InlineCReg.hs`, `-inline-creg`) and the fork's `wiretypemap` knows the inlined names (`src/comp/WireAnalysis.hs`, "cregToReg's port-name rewrite"); a boundary module changes every bypass FIFO's Verilog structure. Option: library selects the reference under `genC` and keeps the BVI for Verilog, as `ZBusUtil.bsv` does (`src/Libraries/Base2/ZBusUtil.bsv:68`), until the equivalence tests justify switching Verilog too. (b) Derived annotations reproduce the BVI's `port_i SBR port_{i+1}` chain by construction (reads of port `i+1` see the port `i` RWire) |

### 5.3 Phase 3b: memories

* `RegFile`/`RegFileWCF` (`src/Libraries/Base1/RegFile.bs:52-192`): a thin
  Bluespec wrapper over the core memory array; the `WCF` variant is an
  annotation-only difference and needs 7.1 to leave the core.
* `BRAM1/1BE/2/2BE` (`src/Libraries/Base2/BRAMCore.bsv:148-780`): reference
  = core array plus output registers with WRITE-FIRST (`src/Verilog/
  BRAM2.v:68`), `EN`-gated read register, `PIPELINED` as a static argument
  selecting the second register (`BRAM2.v:91`), byte enables as a vector of
  writes. `*Load` variants stay on the core until 7.2.
* `DualPortRam` (used by `SyncFIFO`): core array with two clocks; it is the
  storage behind Phase 4.

### 5.4 Phase 4: synchronizers (MCD Bluespec over the crossing core)

`SyncBit`, `SyncBit05/1/15`, `SyncPulse`, `SyncHandshake`, `SyncRegister`,
`SyncFIFO/0/1/10`, `SyncFIFOLevel/0` (`src/Libraries/Base1/Clocks.bsv:
724-1375`, `FIFOLevel.bsv:879-961`): registers `clocked_by` the two domains
with the unsafe crossing done through `CrossingRegN`/`mkNullCrossingReg`,
gray-code pointers as in `src/Verilog/SyncFIFO.v`, `depth` static and
checked to be a power of two at elaboration (replacing the `$finish` in
`SyncFIFO.v:260`). Bluesim already supports MCD rules (`clock_crossing_rule`
handling, `src/comp/SimExpand.hs:316-334`). Known delta to decide: the `.v`
resets the destination domain from the source reset (`SyncFIFO.v:89`,
`dRST = sRST`); the reference should take the same `reset_by` to match.
Equivalence testing here is cycle-level co-simulation with both clocks
driven from the same Verilator testbench, since formal equivalence across
domains is not practical.

### 5.5 Leave as is

`OVLAssertions` (external library), `InoutConnect`/`InoutSplit`/`TriState`/
`ConvertToZ`/`ResolveZ` (inout and tristate; Bluesim does not support them),
`ConstrainedRandom`, `SPSRAM`/`DPSRAM` (already Bluespec under `genC`,
`src/Libraries/Base2/SPSRAM.bs:21`), `JoinClock` (already unsupported in
Bluesim).

## 6. Phase 5: Bluesim removal and cleanup

For each primitive family after its reference lands and the library no longer
emits the BVI name:

1. Delete the `primMap` rows (`src/comp/SimPrimitiveModules.hs:263-348`)
   and the matching `getPrimDomainInfo`/`isFIFO`/`isCReg`/`is*PortBRAM`
   cases (`src/comp/SimPrimitiveModules.hs:390-687`), then the C++
   (`src/bluesim/bs_prim_mod_fifo.h`, `prim_mod_fifo.cxx`, `_counter`,
   `_synchronizers`, most of `_reg.h` except `MOD_Reg`/`MOD_ConfigReg`,
   `_regfile.h`/`_bram.h` down to the core array).
2. Keep an unknown-name error path: once a name is gone from `primMap`, a
   stale `.bo` that still instantiates `FIFO2` must fail with
   `EBSimForeignImport` (`src/comp/ABinUtil.hs:274-285`), which it does
   today for any non-primitive import.
3. Remove the corresponding `src/Verilog/*.v` from `src/Verilog/Makefile`
   only after one release; the equivalence tests keep copies.
4. Expected end state of `primMap`: Reg family (6 rows with Crossing),
   ConfigReg (3), wires (6), memory array (RegFile, RegFileLoad, DualPortRam,
   and `BRAM*Load` until 7.2), clocks (11), resets (9), probes (2), about
   40 of today's 85 rows; `bs_prim_mod_fifo.h`, `_counter.h`,
   `_synchronizers.h` gone.
5. Update `doc/user_guide` (Bluesim primitive list, VCD naming) and the
   libraries reference where it documents Verilog module names.

## 7. Follow-on work

### 7.1 Schedule annotation pinning

Derived annotations are sound but can be *less* restrictive than the BVI
assertions (`first CF deq`, `notFull CF enq`), which can change rule
conflicts in existing designs, and *more* restrictive than intentionally
relaxed primitives (`ConfigReg`, `RegFileWCF`). Add a module pragma
`schedule = [ ... BVI-style annotations ... ]` applied in GenWrap's `deffun`
when building the wrapper's `VSchedInfo` (`src/comp/GenWrap.hs:1463-1536`):

* a declared annotation that is at least as restrictive as the derived one is
  accepted and replaces it (lets the library pin `first SB deq`);
* a declared relaxation (CF where SB was derived) is an error unless marked
  `unsafe_schedule`, which is how `ConfigReg`, `RegFileWCF` and `Counter`'s
  "lie" would leave the core.

About 150 lines in GenWrap plus a comparison function in
`src/comp/SchedInfo.hs`. This is what turns the Phase 4.3 schedule row from
"known delta" into "identical".

### 7.2 Memory file loading

`RegFileLoad`/`BRAM*Load` need `$readmemh`/`$readmemb` at simulation start.
Options: (a) a `primReadMemFile` system-task foreign function usable from a
reference module's initial rule (Verilog: `$readmemh` in an `initial` block;
Bluesim: `read_mem_file`, `src/bluesim/bs_mem_file.h`), which moves the
*array* out of C++ but keeps one tiny runtime hook; (b) elaboration-time
file reading producing a `Vector` of initial values (only for small
memories). (a) is the one consistent with "Bluesim implements no modules".

### 7.3 Parameterized shells (optional)

If a consumer needs a module literally named `FIFO2` with `parameter width`,
a link-time tool can wrap the specializations in a `generate case (width)`
shell over the `FIFO2_<n>` modules present in the design. This is cosmetic
and should not gate anything.

### 7.4 Bluesim performance

Measure FIFO-heavy designs after Phase 2. If the flat-schedule cost of
reference FIFOs matters, the mitigation is in the Bluesim backend
(inlining small leaf modules into the parent's schedule), not in the
primitives.

### 7.5 Upstreaming

Phase 1 is self-contained and upstreamable to B-Lang-org/bsc independently
of the library switch; propose it there with the `-specialize-synth` flag
default off.

## 8. Risks and open questions

1. **Double elaboration** on first discovery (3.6). Acceptable for the
   minimum; measurable; re-entrant child compile is the fix if needed.
2. **Flag-dependent specialization contents** across packages (3.6).
   Advisory warning only in the first version.
3. **Schedule deltas** in existing designs (4.3, 7.1). Phase 0 quantifies
   them on the testsuite; pinning removes them.
4. **CReg in Verilog** (5.2): boundary vs inlined. Decide with the
   equivalence results and the `wiretypemap` consumers.
5. **Bluesim speed** (7.4).
6. **Incremental rebuild** (`-u`) does not know about specializations;
   regenerated with the parent, like DPI wrappers.
7. **Name collisions**: a user module named `FIFO2_32` would collide with a
   specialization. Specializations are generated from a `verilog_name` or
   def name plus a suffix; document the convention and let the registry
   error on a clash with a non-specialization module of the same name.
   Separately, Bluesim (`src/comp/SimPrimitiveModules.hs:354-355`,
   `src/comp/ABinUtil.hs:351-353`) and the formal backends
   (`src/comp/LambdaCalcUtil.hs:1247-1296`) match primitives by `vName`
   string, so a `verilog_name` equal to a `primMap` entry (`FIFO2` without
   suffix, on a monomorphic module) would silently select the C++ model or
   misparse the instance arguments; reject `verilog_name` values that are
   current primitive names while those entries still exist.
8. **`Vector`/struct type arguments** fall to the hashed name form (3.5);
   library cores avoid this by taking numeric parameters only.
9. **Not verified by execution**: this plan was written from reading the
   source; no bsc binary was available in the session. Phase 0 is the
   executable check of every library-side claim, and 3.8 of every
   compiler-side one.

## Appendix A. Port and parameter targets for the replaceable primitives

Headers taken from `src/Verilog/*.v`. A reference implementation must
reproduce the port names and the parameters that are *values*; parameters
that size structure become part of the specialized module name (3.5).

| Verilog module | Ports | Value parameters (stay `parameter`) | Structural parameters (become name suffix) |
|---|---|---|---|
| `FIFO1`, `FIFO2` | `CLK, RST, D_IN, ENQ, FULL_N, D_OUT, DEQ, EMPTY_N, CLR` | `guarded` | `width` |
| `FIFO10`, `FIFO20` | same minus `D_IN, D_OUT` | `guarded` | (width 0 specialization) |
| `FIFOL1`, `FIFOL2` | as `FIFO1` | none | `width` |
| `SizedFIFO` | as `FIFO1` | `guarded` | `p1width`, `p2depth` (`p3cntr_width` is derived) |
| `SizedFIFOL` | as `FIFO1` | none | `p1width`, `p2depth` |
| `Counter` | `CLK, RST, Q_OUT, DATA_A, ADDA, DATA_B, ADDB, DATA_C, SETC, DATA_F, SETF` | `init` | `width` |
| `CRegN5` | `CLK, RST, Q_OUT_i, EN_i, D_IN_i` for i in 0..4 | `init` | `width` (and port count `n`, today fixed at 5) |
| `RegTwoN` | `CLK, RST, Q_OUT, D_INA, ENA, D_INB, ENB` | `init` | `width` |
| `RevertReg` | `CLK, Q_OUT, D_IN, EN` | `init` | `width` |
| `McpRegUN` | `CLK, RST, SET, val, get` | none | `width`, `delay` |
| `RegFile` | `CLK, ADDR_IN, D_IN, WE, ADDR_i, D_OUT_i` for i in 1..5 | `lo`, `hi` as values if the core array takes them | `addr_width`, `data_width` (core primitive, 5.1) |
| `BRAM1` / `BRAM2` | `CLK, EN, WE, ADDR, DI, DO` / `CLKA..DOA, CLKB..DOB` | none | `PIPELINED`, `ADDR_WIDTH`, `DATA_WIDTH`, `MEMSIZE` |
| `BRAM2BE` | as `BRAM2` | none | plus `CHUNKSIZE`, `WE_WIDTH` |
| `SyncBit` | `sCLK, sRST, dCLK, sEN, sD_IN, dD_OUT` | `init` | none |
| `SyncRegister` | `sCLK, sRST, dCLK, sEN, sRDY, sD_IN, dD_OUT` | `init` | `width` |
| `SyncFIFO` | `sCLK, sRST, dCLK, sENQ, sD_IN, sFULL_N, dDEQ, dD_OUT, dEMPTY_N` | none | `dataWidth`, `depth`, `indxWidth` (derived) |
| `SyncHandshake` | `sCLK, sRST, dCLK, sEN, sRDY, dPulse` | `init`, `delayreturn` | none |
| `SyncPulse` | `sCLK, sRST, dCLK, sEN, dPulse` | none | none |
| `DualPortRam` | `CLK, WE, WADDR, DIN, RADDR, DOUT` | none | `addrWidth`, `dataWidth` (core, 5.1) |
| `ProbeWire` | `OUT, IN` | none | `size` |

Clock and reset port names other than `CLK`/`RST` (`sCLK`, `dCLK`, `sRST`,
`CLKA`, `CLKB`) are set with the existing `clock_prefix`/`reset_prefix`
pragmas for single-clock modules and with explicit `Clock`/`Reset` module
arguments plus `port`-style argument naming for multi-clock ones
(`src/comp/IExpand.hs:1015-1060`, `makeArgPortId`).
