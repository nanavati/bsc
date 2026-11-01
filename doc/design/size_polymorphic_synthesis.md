# Size-polymorphic synthesis boundaries and a Bluespec-native primitive library

Status: proposal / implementation plan, revision 3. Written against this
fork at `99677cb` (branch `claude/size-polymorphic-verilog-qhy2o1`). All
paths are relative to the repository root; `file:line` references were
checked against that revision by reading the source. No bsc binary was run
while writing this; Phase 0 (section 5.2) is the executable check of the
library-side claims and section 3.11 of the compiler-side ones. Appendix B
lists what was verified and how.

## 0. Summary

Goal: Bluesim should stop implementing primitives in C++. Every primitive
that can be written in Bluespec gets a reference Bluespec implementation that
the Bluesim backend, the formal paths and (per family, when its consumers
agree) the Verilog backend all use, and `src/bluesim/bs_prim_mod_*.h` shrinks
to an irreducible core. The barrier is that a `synthesize` boundary must be
monomorphic (`src/comp/GenWrap.hs:423-467`), so a polymorphic `mkFIFO2 ::
(Bits a sa) => Module (FIFO a)` cannot be a separate module the way
`FIFO2.v` with `parameter width` is.

Recommendation in one sentence: do not emit `parameter width` Verilog;
instead let a `synthesize` module marked `specialize` be synthesized once per
distinct instantiation, named from its type and static arguments, with the
child compiled re-entrantly from the parent's elaboration (the design quark17
describes in B-Lang-org/bsc issue #921). The Verilog backend, the Bluesim
backend and the `.ba` link flow already work on exactly this shape; the new
machinery is an evaluator node for specializable references, a late
GenWrap-plus-typecheck pipeline for the generated aliases, and a registry.

Three things the first revision of this plan got wrong, now fixed:

* **Bluesim first.** The library selects the reference core under `genC`
  and keeps the hand-written `import "BVI"` under `genVerilog`, the pattern
  `ZBusUtil.bsv` already uses (`src/Libraries/Base2/ZBusUtil.bsv:68`). That
  removes every Verilog-side risk (duplicate `.v` outputs in explicit-file
  Verilog compiles, CDC and STA constraints keyed on `SyncBit.v` register
  names, monorepo Verilog structure tests) from the critical path. The
  Verilog-side switch is a per-family decision taken with the consumers, and
  a new `-prim-impl` flag (4.3) makes it available per design for formal
  work.
* **Schedule and port-type fidelity are prerequisites, not follow-ons.**
  Derived annotations are *not* a harmless relaxation at the Bluespec level
  (`first CF deq` lets a rule `deq` then `first`), and the planned port-type
  override does not work because `savePortType` is first-wins
  (`src/comp/IExpandUtils.hs:1265-1275`). Both are addressed in Phase 1b
  (section 4), using `mkRevertingVirtualReg` ordering tokens in the wrapper
  for the former and a small compiler fix for the latter.
* **The evaluator hook is a node, not a side condition.** Module constructors
  are routinely passed unapplied (`mapM mkFoo xs`, `genWithM`), heaped and
  applied later, so a check inside `evalAp'`'s `ICDef` clause would silently
  lose boundaries. Specializable references get their own `IConInfo`
  (3.4).

Phase 1 (compiler) is 1500 to 2500 lines of Haskell plus tests; start with a
spike of the evaluator node and the re-entrant compile on a two-module
example before any GenWrap work.

## 1. What the compiler does today

### 1.1 The monomorphism gate is GenWrap's, and the rest of the pipeline is already per-module

* `genWrapE` runs before type checking (`src/comp/bsc.hs:386-436`). For each
  def carrying `PPverilog` it calls `chkType`, which rejects any remaining
  proviso ("It has a proviso." / "context" in Classic, `:429-432`), any free
  type variable ("Its interface is polymorphic.", `:435-437`), a polymorphic
  interface field (`:445-450`), a non-interface or non-module type
  (`:460-467`). The only proviso it tolerates is a single `IsModule`, which
  `fixupPolyModType` ties to `Module` (`src/comp/GenWrap.hs:583-598`; it
  matches exactly one remaining predicate).
* The data structures anticipate this feature: `IfcTRec.rec_numargs` /
  `rec_typemap` "Until we support synthesis of size-parameterized modules"
  (`src/comp/GenWrap.hs:170-187`); `imod_type_args` "always empty"
  (`src/comp/ISyntax.hs:156-159`); `iks = []` (`src/comp/IExpand.hs:
  816-818`); `aspkg_parameters` "XXX there are no size parameters because we
  don't support synthesis of size-polymorphic modules" (`src/comp/ASyntax.hs:
  258`); `ENotKNum` "Only size polymorphism allowed in code generation" is
  defined and never raised (`src/comp/Error.hs:2228`).
* GenWrap produces, per synthesized `mkFoo`: a flattened interface struct
  named from the interface *type* (`flatTypeIdQual`, `src/comp/GenWrap.hs:
  1879-1902`), `to_`/`from_` conversions and a `Generic` instance
  (`:1048-1260`), an inner def `mkFoo<soft hyphen>` of type `Module Foo_`
  that let-binds the user's def and applies it to the converted arguments
  (`:1314-1451`, `mexp = cApply 10 (CVar i) exprs` at `:1356`), and a
  continuation `deffun` that, after the backend has run, builds the wrapper as
  `liftModule (CmoduleVerilog ...)` keeping the def's *original* `CQType`
  (`:1463-1536`, `:1531`; `src/comp/CSyntax.hs:573-612`). The driver then
  rebuilds the symbol table "because GenWrap added new types and typeclass
  instances", derives, context-reduces, converts instances and typechecks
  (`src/comp/bsc.hs:395-436`). The wrapper is typechecked late by
  `compileCDefToIDef` against the frozen symbol table and spliced in by
  `updDef` (`src/comp/bsc.hs:2314-2345`, `src/comp/FixupDefs.hs:222-257`).
* Argument port and parameter names come from the clause binders:
  `getDefArgs` takes `CPVar` names (`src/comp/GenWrapUtils.hs:72-90`, falling
  back to `a1000...` for a point-free def), `iExpandModulePortArgs` names the
  port from the `ILam` binder (`src/comp/IExpand.hs:1086-1113`), and every
  argument-naming pragma is checked against those names
  (`src/comp/PragmaCheck.hs:147-232, 389-410`, `EAttributeNoSuchArg`).

### 1.2 Everything needed to instantiate a child by a computed name exists

* The Verilog module name of a `module verilog` import is a String-typed
  *expression* evaluated at elaboration: `handlePrim` calls `evalString name`
  and sets `vName` (`src/comp/IExpand.hs:1693-1724`; Classic parser rule
  `src/comp/Parser/Classic/CParser.hs:131`). The library already picks a
  module per size this way (`src/Libraries/Base2/SPSRAM.bs:70-77`, exercised
  by `testsuite/bsc.interra/libraries/SyncRAM/`). BSV `import "BVI"` takes an
  identifier (`src/comp/Parser/BSV/CVParser.lhs:4645-4654`), so this is
  Classic-only.
* The backend instantiates whatever `vName` says (`src/comp/AVerilogUtil.hs:
  1115-1120`). Instance parameters come from `Param` args (`:1088-1097`); a
  synthesized module's own parameters come from `param` arguments
  (`src/comp/IExpand.hs:1086-1113`, `src/comp/AVerilog.hs:440-453`) and this
  fork supports `Integer`-typed ones (commit `e246d69`, upstream PR #1034).
  A parent parameter can be forwarded to a child parameter
  (`src/comp/AVerilog.hs:1237-1241, 1571-1589`).
* Per-width monomorphization by name is already a fork pattern: polymorphic
  DPI functions become `f_w32_w8` per distinct width set
  (`src/comp/ForeignFunctions.hs:555-587`, `src/comp/AVerilogUtil.hs:
  1237-1241`). Classic `foreign` functions pass numeric type variables as
  named instance parameters (`src/comp/MakeSymTab.hs:817-866`,
  `src/Libraries/Base1/Fork.bs:18`, `src/Verilog/Fork.v:7-10`).
* Imported polymorphic bodies are available downstream: the `.bo` stores
  every `IDef` with its body (`src/comp/GenBin.hs:555-558`), `fixupDefs`
  re-ties `ICDef` pointers across packages (`src/comp/FixupDefs.hs:
  179-215, 266-268`), and `evalAp'` on `ICon i (ICDef t e)` evaluates the
  body in place (`src/comp/IExpand.hs:3365-3382`). After typecheck a
  variable use is `CApply (CTApply f types) dictVars` applied to values
  (`src/comp/TCheck.hs:1775-1780, 3282`), so the argument stack is type
  args, then dictionary args (binders carry `IdPDict`, `src/comp/Id.hs:
  532-533`), then values (`src/comp/IExpand.hs:3402-3403`).
* Package pragmas are serialized into the `.bo` (`src/comp/GenBin.hs:
  536-541`) with package-qualified ids (`src/comp/IConv.hs:66-67`), and an
  importing package's `ipkg_pragmas` carries its transitive imports' pragmas
  (`src/comp/FixupDefs.hs:197`). `-g` names exist only in GenWrap's `ppmap`
  (`src/comp/GenWrap.hs:263-288`) and never reach the `.bo`. The `CSignature`
  keeps only `PPdeprecate` (`src/comp/GenSign.hs:477-488`).

### 1.3 Why true parameterized Verilog is not the minimum

* `type ASize = Integer` (`src/comp/ASyntax.hs:520`); every size in ASyntax,
  every literal width (`src/comp/IntLit.hs:14-16`), the `.ba` format
  (`src/comp/BinData.hs:1017-1027`) and Bluesim's `aTypeToCType`
  (`src/comp/SimCCBlock.hs:366-372`) assume a literal. `PrimValueOf` on a
  non-`ITNum` is an internal error (`src/comp/IExpand.hs:3948-3952`);
  `chkStateVarTypes` rejects free type variables in state (`:1871-1885`).
* The evaluator is a concrete-width partial evaluator: `doPrimOp` binds
  result widths from `[i | ITNum i <- ts]` (`src/comp/IPrims.hs:26-37`) and
  the strict-primitive folding path passes only `ITNum` type args
  (`src/comp/IExpand.hs:4337-4364`). The fork's lazy pack/unpack
  (`ICLazyPack`/`ICLazyUnpack`, `:4019-4062`) keeps a payload opaque by
  *type*, not by width.
* Width-dependent rewrites are everywhere downstream: AOpt masks and extract
  bounds (`src/comp/AOpt.hs:584, 847-878, 1398-1464`), AVeriQuirks
  (`src/comp/AVeriQuirks.hs:207-237`), the SAT disjointness tests
  (`src/comp/AExpr2STP.hs:424-512`), zero-width elision at a dozen sites
  (`src/comp/AVerilog.hs:171-172, 384-390`, `src/comp/AVerilogUtil.hs:
  969-1070`). The only symbolic widths bsc emits are the hand-built `Mux_n`
  primitives (`src/comp/VPrims.hs:21-34`).
* For a FIFO the data registers *are* the parameter, so there is no
  restricted class of modules whose body stays width-concrete.

### 1.4 Bluesim needs monomorphic `.ba` modules with unique names, and nothing else

* The link-time hierarchy walk partitions instances by `avi_user_import`,
  not by name: a non-user-import instance is followed by name and its
  `<name>.ba` is read from the `-p`/`-bdir` path (`src/comp/ABinUtil.hs:
  254-257, 345-357, 390-424`); a user-import (`import "BVI"` or Classic
  `module verilog`) whose name is not in `primMap` is `EBSimForeignImport`
  regardless of whether a `.ba` exists (`:268-285`). GenWrap's wrappers are
  built with `is_user_import = False` (`src/comp/CSyntax.hs:584-600`), so a
  synthesized module is followed. Name tables are then consulted by name
  alone in `SimMakeCBlocks.hs:634, 728, 937`, `SimCOpt.hs:118`,
  `SimFileUtils.hs:111`.
* One C++ class per module type (`src/comp/SimMakeCBlocks.hs:72-114`,
  `src/comp/SimCCBlock.hs:1692`), schedules flattened into the parent
  (`src/comp/SimExpand.hs:758-1112`), hierarchy kept for VCD scopes and
  Bluetcl `sim cd/ls/lookup` (`src/comp/SimCCBlock.hs:1986-1997`,
  `src/comp/bluetcl.hs:2656-2722`). Register primitives are not inlined in
  Bluesim: `MOD_Reg` dumps one flat def named by the instance
  (`src/bluesim/bs_prim_mod_reg.h:156-161`).
* The C++ FIFO mimics the Verilog ports in its VCD scope (`FULL_N, EMPTY_N,
  ENQ, D_IN, DEQ, CLR, D_OUT`, `src/bluesim/bs_prim_mod_fifo.h:263-293`) but
  not the internal names (`arr_0` vs `data0_reg`), prints `Warning: <inst>
  -- Dequeuing from empty fifo` without the Verilog's `FIFO2:` prefix
  (`:104-108, 138-142` vs `src/Verilog/FIFO2.v:140, 145`), and drops the
  overflowing element on enqueue-when-full where `FIFO2.v:66` overwrites
  `data1_reg`. Bluesim `$display` supports `%m` (`src/bluesim/
  dollar_display.cxx:949-950`, instance path without the simulator's
  testbench prefix).
* Unless `-keep-fires` is given, `SimCOpt.moveDefsOntoStack` moves every
  def referenced by one function (CAN_FIRE/WILL_FIRE and single-use method
  ports) off the class, so they are absent from the VCD
  (`src/comp/SimCOpt.hs:176-206, 258-266`).

### 1.5 Formal backends see boundaries as opaque constructors

LambdaCalc/SAL are produced from the in-memory `APackage` inside `genModule`
(`src/comp/bsc.hs:854-860`), not from `.ba`, with no link step. They have
their own name-keyed primitive table (`src/comp/LambdaCalcUtil.hs:
1257-1322`); any other submodule is emitted as an opaque constructor call
named by `vName` (`src/comp/LambdaCalc.hs:681-686`, `src/comp/SAL.hs:
855-860`), already the case today for the zero-width FIFO names, which are
not in that table. So a per-size reference module is a separately dumped
unit that the formal flow composes itself, which is what compositional
equivalence wants; a design that wants the reference *inlined* uses the
un-synthesized reference module, which is the same source. The golden
`testsuite/bsc.misc/lambda_calculus/lambda_calculus.exp:139-146`
(`MOD_FIFO2 #1` and friends) changes when the FIFO names leave the table.

### 1.6 Upstream context

* The BSV reference guide states the limitation and its cause
  (`doc/BSV_ref_guide/BSV_lang.tex:3216-3219`), documents the per-type alias
  workaround (`:3125-3131`), says parameters cannot drive structure
  (`:2178-2185`), and the bluetcl chapter documents `InstSynth.tcl`
  (`doc/user_guide/bluetcl.tex:876-980`, `util/bluetcl-scripts/
  InstSynth.tcl`), which this plan replaces.
* Issue #543 (2023) asks for width-as-parameter; quark17 lists the obstacles
  (overloaded operations, conditional instantiation on `valueOf`, unrolled
  loops). Issue #921 (nanavati, 2026-04, "allow synthesize pragmas on
  instantiations") is the closest relative: quark17's comment says "I had
  always assumed that we'd implement submodule synthesis by discovering them
  during elaboration: BSC would elaborate until it found such a submodule,
  then would have to stop and elaborate the submodule ... and then come
  back", and names three levels (concrete type at typecheck; pragma inside a
  polymorphic parent; `Integer` arguments known only at elaboration). Section
  3 is that design and covers all three levels. Issue #824 wants the special
  FIFOs visible as modules in VCDs; issue #1063's `WrapInterface` idea is
  compatible (3.6 needs *a* wrapper generator for a monomorphic alias).
* Merged upstream precedents in this fork: `WrapField`/`SplitPorts` (PR
  #729), named foreign instance parameters (PRs #1022, #1023), Integer
  module parameters (PR #1034), DPI monomorphization (PR #999).

## 2. Options considered

| Option | What changes | Verdict |
|---|---|---|
| A. Demand-driven specialization: a `specialize`d `synthesize` module is synthesized once per distinct instantiation, compiled re-entrantly from the parent's elaboration | GenWrap gate; one evaluator node; late alias pipeline; registry; naming | **Chosen.** Reuses the whole existing pipeline; Bluesim and formal get real boundaries; names are stable |
| B. Emit `parameter width` Verilog from one elaboration | Symbolic `ASize` through AConv, AState, AOpt, AVeriQuirks, ASchedule/SAT, AVerilog, BinData, Bluesim | Rejected. A multi-month rewrite that loses SAT on width-dependent logic; Bluesim still needs per-width classes |
| C. Library-only: explicit per-width aliases, `mkUCount`-style ladders, computed `module verilog` names plus `InstSynth.tcl` | No compiler change | The Phase 0 prototype only. Classic-only computed names, hand-maintained alias lists, and nothing checks a hand-written BVI schedule against the module it names |
| D. Witness elaboration: elaborate at two template widths, fit, substitute a parameter name in AVerilog | AVerilog-only post-pass | Fragile (AOpt folds differ by width, zero-width elision). Possible cosmetic follow-on (8.4) |

## 3. Phase 1: demand-driven specialization in the compiler

### 3.1 Semantics

A module def marked `synthesize` *and* `specialize` (`{-# verilog mkFoo {
specialize } #-}` in Classic, `(* synthesize, specialize *)` in BSV) is
**specializable**. No Verilog is produced when its own package is compiled.
Each instantiation at concrete type arguments and static argument values
(3.2), in any later elaboration, produces one monomorphic synthesized module
named from those arguments (3.5), compiled at that moment (3.4, 3.6), and the
parent instantiates it as a submodule. Identical (def, type args, static
args) anywhere in the design map to the same module name, generated once per
compile and reused across packages that import the generating one (3.7).

`specialize` is explicit rather than inferred so that `Depend.hs` can skip
these defs without type information (3.8), accidental polymorphism keeps
today's error, and `-g` on a specializable def is a separately diagnosed
case (3.10). Everything else about the module is unchanged: `param`
arguments become Verilog parameters, `Bits` arguments become ports, clocks
and resets become ports, port-naming attributes apply, `.ba` is written in
`-sim` and `-elab` modes.

Definition-site versus instantiation-site marking: issue #921 proposes a
pragma on the *instantiation*. The primitive library needs the
definition-site form (every instantiation of the reference `mkFIFO2` must get
a boundary without the user annotating it). The two forms share the
mechanism; the instantiation form is a later step (8.6).

### 3.2 Static arguments

Today an `Integer`, `String` or `Real` argument on a synthesis boundary must
be marked `parameter`, else `EParamOnlyType` (`src/comp/IExpand.hs:
1101-1102`); the check runs only for the def being generated
(`iExpandModuleLam`, `:945-990`), so a polymorphic def with such arguments
compiles fine as long as it is not itself generated. For specializable
modules the new rule is: such an argument *without* `parameter` is a
**static argument**: part of the specialization key, required to be a
literal at the instantiation, mangled into the module name. This is what
`SizedFIFO`'s depth needs (it sizes storage, which a Verilog parameter
cannot, `doc/BSV_ref_guide/BSV_lang.tex:2178-2185`) and is the same
distinction the library makes between `p2depth` and `guarded`
(`src/Libraries/Base1/FIFOF_.bsv:235-240`). With `parameter`, the existing
behavior (a Verilog parameter) is kept.

Rules that follow:

* Static positions are identified from the def's *type*, not by position in
  the argument list: they may be interleaved with `Clock`, `Reset` and port
  arguments.
* A static argument whose value is a parent `parameter` (`ICModParam`) is
  constant but not a literal and is an error (parallel to
  `EModParameterDynamic`, `src/comp/Params.hs:95-100`); so is any other
  non-literal. Evaluation uses `evalInteger` (`src/comp/IExpand.hs:
  2599-2604`) and `evalString` (`:2478-2484`); `Real` needs a small new case
  on `ICReal`.
* Arguments of interface, function or `Module` type are a definition-site
  error for specializable modules, as they are for synthesized modules today
  (`src/comp/GenWrap.hs:437-452, 1484-1486`).
* The depth-parameter FIFOs (`mkDepthParamFIFOF_`, `mkDepthParamLFIFOF_`,
  `src/Libraries/Base1/FIFOF_.bsv:345-372, 606-637`) take a parent Verilog
  `parameter` as depth (`testsuite/bsc.lib/fifo/depth_param/FIFOParam.bsv`)
  and therefore cannot be specialized; they stay BVI imports of `SizedFIFO.v`
  or are deprecated (6.5).

### 3.3 GenWrap and front-end changes

1. `src/comp/Pragma.hs`: new `PProp` constructors `PPspecialize` and
   `PPverilogName String`; Classic spellings `specialize` and `verilog_name =
   "..."` in `pVeriGenProps` (`src/comp/Parser/Classic/CParser.hs:635-660`),
   BSV attributes `specialize` and `verilog_name`. Both need `Bin PProp`
   cases (`src/comp/BinData.hs:785-830`) and a `.bo` header bump
   (`src/comp/GenBin.hs:26-30`).
2. `getDef`/`chkType`: for a def with `PPverilog` and `PPspecialize`, when
   `generating`, do not create a `WrapInfo` and do not `fixDef` the body;
   strip `IsModule` from the context before classifying (today
   `fixupPolyModType` handles only a single-predicate context,
   `src/comp/GenWrap.hs:583-598`); keep erroring on the gates that type
   arguments cannot fix (polymorphic *fields*, non-interface, non-module,
   interface/function arguments). Without `PPspecialize`, behavior is
   unchanged (the existing errors).
3. The `CPragma (Pproperties mkFoo [PPverilog, PPspecialize, ...])` is a
   source pragma, so it reaches `ipkg_pragmas` unchanged (1.2) and importers
   can find specializable ids by qualified name. The registry scan must
   dedupe across `binmods`, since each `.bo` repeats its imports' pragmas.
4. `Depend.hs:193-194` and `bluetcl.hs:786-791`: exclude `PPspecialize` defs
   from `gens` and from `defs module` (otherwise `-u` expects `mkFIFO2.v`
   forever, the failure mode described at `src/comp/Depend.hs:230-241`).
5. `-g mkFoo` on a specializable module: new error, "`mkFoo` is
   specialized per instantiation; instantiate it from a synthesized module
   or give it a monomorphic alias".
6. `verilog_name` is used only as the *base* of the mangled name (3.5). The
   alias def itself is named by the mangled string, so the wrapper literal
   (`src/comp/GenWrap.hs:1525`), `apkg_name` (`src/comp/AConv.hs:313`), the
   `.v`/`.ba` file names (`modstr`, `src/comp/bsc.hs:733, 1042, 1081`) and
   Bluesim's lookup by `vName` all agree with no further plumbing. Honoring
   `verilog_name` on *monomorphic* modules would additionally need
   `Depend.getGenFs` and bluetcl `defs module` changes and is deferred.

### 3.4 Specializable references in the evaluator

`fixupDefs` (`src/comp/FixupDefs.hs:179-215`) installs, for every id in the
specializable set, a new `IConInfo`:

```
ICSpecDef { specKey    :: Id            -- qualified def id
          , specType   :: IType         -- the def's scheme
          , specArity  :: Int           -- type args + dicts + statics to collect
          , specStatic :: [Int]         -- positions of static args among value args
          , specBody   :: IExpr }
```

instead of the plain `ICDef`. `conAp'` treats it like a fixed-arity
primitive: it accumulates `T` and `E` arguments into a WHNF partial
application until the static prefix is saturated, then acts. This is the
only sound place: module constructors are routinely passed unapplied
(`mapM mkFoo xs`, `zipWithM`, `genWithM`; 154 such sites in `src/Libraries`
and `testsuite`), heaped (`toHeap`, `src/comp/IExpandUtils.hs:2833-2845`)
and forced later with an empty stack (`src/comp/IExpand.hs:3425-3440`), and
a bare `ICon i (ICDef ..)` passed as a value is heaped as its body
(`:2842-2844`); a side condition in `evalAp'`'s `ICDef` clause would miss
both and silently inline. `ISimplify.expDef` must likewise leave `ICSpecDef`
alone (`src/comp/ISimplify.hs:47-54, 168-179`).

When saturated:

1. Partition the type arguments: those bound by the def's `IsModule m c`
   proviso (BSV `module` syntax and most of the library are `(IsModule m c,
   ...) => m Ifc`, `src/Libraries/Base1/FIFO.bs:52-101`) are *not* part of
   the key; the rest are normalized with `fullTypeNormalizer`
   (`src/comp/IExpandUtils.hs:2576-2611`) and must be fully concrete (else an
   error at the application: "type arguments of specializable module `mkFoo`
   could not be determined"). Static arguments are evaluated to literals
   (3.2).
2. Key = (qualified id, specialized type args, static values); name =
   `mangle` (3.5).
3. If the key equals the specialization currently being generated
   (`g_current_spec` in `GStateRO`), **inline** the body: the alias's own
   inner def is `let mkFoo_32 = \g -> mkFoo @32 d g in mkFoo_32 ...`
   (`src/comp/GenWrap.hs:1356, 1373`), so every specialization reaches its
   own key once. If the key is on the active generation stack but is not the
   current one, it is a genuine cycle: error naming the chain. No fixed
   depth limit (a linear recursive `mkTree n` over 100 stages is legitimate).
4. Look the name up in the registry (3.7). On a miss, call the driver
   callback `g_specialize :: SpecKey -> IO IDef` (3.6), which compiles the
   child, writes its `.v`/`.ba`, inserts its wrapper into the registry and
   returns it. `G` is `StateT GState IO` with a fresh `GState` per `runG`
   and no global mutable state beyond per-heap `IORef`s
   (`src/comp/IExpandUtils.hs:492, 617-703`), so a nested `genModule` is an
   ordinary `lift`ed IO action. Recursion depth equals hierarchy depth.
5. Redirect: apply the registry wrapper to `T m, T c, E isModuleDict` (the
   wrapper is `liftModule`-based and keeps the def's `IsModule` polymorphism,
   `src/comp/GenWrap.hs:1531, 553-556`) followed by the remaining value
   arguments with the static positions removed. `clocked_by`/`reset_by` wrap
   the *result* (`primModuleClock :: Clock -> Module a -> Module a`), so they
   are unaffected; instance naming comes from the parent's binder through
   `IStateLoc`/`PrimModuleBind` (`src/comp/IExpand.hs:1587-1622`), and
   `handlePrim`/`newState` read only the wrapper's `VModInfo`
   (`:1693-1724, 1896-1947`).

Why not two passes: a discovery pass that inlines and records demands was the
first design. It would run the whole `genModule` (writing the parent's `.v`
and `.ba` with the child inlined, possibly `exitFail`ing on a schedule error
the boundary form would not have, and re-emitting every warning and dump,
since `ErrorHandle` keeps no seen-set, `src/comp/Error.hs:137-153`, and
`dumpStr` appends, `src/comp/TopUtils.hs:124-130`), and it cannot be
amortized by a static pre-scan because nearly all library demands are reached
through the polymorphic chain `mkFIFOF -> mkFIFOF_ -> mkFIFOF2_ ->
vMk2FIFOF`. The re-entrant form is both simpler and what #921 asks for.

### 3.5 Naming

`mangle :: Id -> [IType] -> [static value] -> String`:

* base = `verilog_name` if present, else the def's base name;
* reuse GenWrap's own type flattening (`flatTypeIdQual`,
  `src/comp/GenWrap.hs:1879-1902`, which already names the flattened
  interface struct per type) with `_` separators: `ITNum n` → decimal;
  `Bit 32` → `Bit32`; `Bool` → `Bool`; an `Integer` static → decimal
  (negative as `m<n>`); a `String` static → the string if it is a legal
  identifier fragment, else hashed;
* if the result exceeds 64 characters or any argument needed replacement,
  use `<base>__h<16 hex digits of a hash of the canonical key>` so names stay
  legal for Verilog, file systems and C++ (`MOD_<name>`). Hash the canonical
  `pfpString` of qualified id and types, never pointer identities.

Library reference cores take only numeric type parameters (like `VReg n`,
`src/Libraries/Base1/Prelude.bs:1989`) and static `Integer`s, so they always
get the readable form: `FIFO2_32`, `FIFO2_0`, `SizedFIFO_32_16`,
`Counter_8`. The key is the full type-argument list, not the widths they
imply: `Maybe (Bit 7)` and `Bit 8` are different specializations of a module
polymorphic in `a`, because the body may use `a` through `Eq` or `FShow`.
Library cores avoid the question by taking `Bit n` payloads and letting the
wrapper `pack`/`unpack`.

Specialized names always carry a suffix and therefore never equal a
hand-written primitive's `vName`, which matters because Bluesim
(`src/comp/ABinUtil.hs:150-152`, `src/comp/SimMakeCBlocks.hs:634`), bluetcl
(`src/comp/bluetcl.hs:1043-1046`) and the formal table
(`src/comp/LambdaCalcUtil.hs:1257-1269`) match primitives by exact name.
Reject a `verilog_name` that equals a current primitive name.

### 3.6 The child compile

`g_specialize key` runs, inside the parent's elaboration:

1. **Alias.** Build a `CDef` named `mangle key` in clause form with the
   original `ILam` binder names (`FIFO2_32 guarded = mkFIFO2 guarded`, never
   point-free: `getDefArgs` would fall back to `a1000...` names and every
   argument pragma would fail `EAttributeNoSuchArg`). Its `CQType` is the
   def's scheme with the specialized type variables substituted (`iToCT`)
   and the static argument positions removed; its body applies `mkFoo` to
   literals at the static positions and to the binders elsewhere. Copy the
   def's module-level `Pproperties` onto the alias, minus `PPspecialize`
   and `PPdeprecate`: this single pragma list is what GenWrap's `ppmap` and,
   through `WrapInfo.wi_prags`, IExpand's `getPragmas`, AConv and
   `abmi_pps` all read (`src/comp/GenWrap.hs:252-276, 637`,
   `src/comp/IExpandUtils.hs:657, 3753`, `src/comp/bsc.hs:728-741, 1056`).
   Pragmas whose payload names arguments (`PPparam`, `PParg_param`,
   `PParg_port`, `PParg_clocked_by`, `PParg_reset_by`, `PPclock_osc`,
   `PPclock_gate`, `PPreset_port`, `PPgate_inhigh`, `PPgate_unused`,
   `PPgate_input_clocks`, `PPclock_family`, `PPclock_ancestors`,
   `PPdefault_clock_arg`, `PPdefault_reset_arg`) are why the binder names
   must be reused; method-name pragmas (`always_ready`, `always_enabled`,
   `enabled_when_ready`, `PPmethod_scheduling`, `PPperf_spec`) copy as is.
2. **Round pipeline.** Put the alias into a synthetic `CPackage` holding the
   current package's type, class and instance defs plus the import
   signatures, and run the same sequence the driver runs today
   (`src/comp/bsc.hs:386-436`): `genWrapE` → `mkSymTab` → `derive` →
   `mkSymTab` → `cCtxReduceIO` → `mkSymTab` → `cConvInst` → `cTypeCheck` →
   `simplify` → `iConvPackage` → merge the new `IDef`s and type/instance
   defs into the current `IPackage` → `fixupDefs`. `compileCDefToIDef` is
   not a sufficient precedent: it typechecks one def against the frozen
   symbol table, while GenWrap adds a struct, a `Generic` instance and
   conversion defs that the symbol table must know before the inner def
   typechecks (the wrapper's `vMethTs` are computed from the symbol-table
   entry of the flattened interface, `src/comp/IConv.hs:589, 625-629`).
   Batch all keys demanded in one round into one synthetic package, and skip
   `IfcTRec`s whose flattened-interface id already exists: the struct, its
   `to_`/`from_` defs and instances are named from the *interface type*, so
   two specializations with the same result type (or one sharing a type with
   a monomorphic module already in the package) would otherwise collide
   (`EMultipleDecl`/`EDuplicateInstance`, `src/comp/MakeSymTab.hs:151,
   446`). Thread the extended symbol table and `alldefs` into every later
   `genModule` and `compileCDefToIDef` (today both are fixed before the
   loop, `src/comp/bsc.hs:535-544, 558-563`; `getDefEnv` is used to convert
   late `CExpr`s, `src/comp/IExpand.hs:5822`).
3. **Generate.** Run `genModule` on the inner def with `g_current_spec =
   key` (so its own body inlines), which recursively specializes
   grandchildren, writes the child's `.v` and `.ba`, then run its `deffun`,
   `compileCDefToIDef` the wrapper, tag the wrapper id `IdPSpecialization`
   (new `IdProp` with a `Bin IdProp` tag, `src/comp/BinData.hs:712-779`,
   `src/comp/Id.hs:133-160`; `.bo`/`.ba` header bumps), add it to the
   package with `updDef`, and insert it into the registry.
4. **Visibility.** The new defs are created after the signatures were
   computed (`genUserSign`/`genEverythingSign` run over the pre-loop
   `CPackage`, `src/comp/bsc.hs:665-669`), so they are in neither `bi_sig`
   nor `bo_sig` and reach importers only through `ipkg_defs` and `alldefs`,
   which is what the registry needs. Extend `defExport`
   (`src/comp/GenSign.hs:538-546`) to drop `IdPSpecialization` ids as well,
   so that a later signature regeneration (bluetcl `bpackage search`,
   `bpackageview`) does not surface them. Note that the `IdPGeneratedIfc`
   rule there hides from *both* signatures, not only the user one.

### 3.7 Registry, reuse, link behavior, builds

* **Registry** = `Map String IDef` seeded from every loaded package's
  `ipkg_defs` tagged `IdPSpecialization` (reuse therefore requires the using
  package to import, transitively, the generating one; siblings regenerate)
  plus what this compile generates.
* **Link facts** to state in the user documentation: Bluesim and the Verilog
  linker find `<name>.ba` on the `-p`/`-bdir` path and dedupe modules
  discovered during the hierarchy walk by name (`src/comp/ABinUtil.hs:
  345-357, 380-386`); two `.ba` of the same name *listed* on the command line
  are an error (`EMultipleABinFilesForName`, `:417-421`); the same name in
  two path directories takes the first with a warning
  (`src/comp/FileIOUtil.hs readFilesPath'`); the same `-bdir` is silently
  overwritten (`src/comp/bsc.hs:1044-1067`); a `.ba` written by a Verilog
  compile cannot be linked by Bluesim (`EABinFileBackendMismatch`,
  `:506-534`); `.ba` content hashing is disabled (`src/comp/GenABin.hs:
  46-51`); `abmi_flags` is fully serialized (`src/comp/ABin.hs:65`).
* **Flags.** Compile library specializations with a canonical flag profile
  (the library's defaults, not the parent's `-aggressive-conditions`,
  `-opt-undetermined-vals`, `-unspecified-to`, `-keep-fires`), record the
  profile in `abmi_flags`, and make a same-name mismatch at link an error,
  not a warning. Design-local specializable modules use the compiling
  package's flags.
* **Hermetic builds.** Per-package build rules (MatX's `bs_library`) declare
  outputs up front and cannot have two actions produce the same path.
  Decide before Phase 2: (a) bsc writes a manifest of generated
  specializations and the rules move `-vdir`/`-bdir` to directory outputs
  propagated to the link steps; or (b) the `.bo` registry stores only *keys*
  and each top-level compile regenerates missing specializations into its
  own output directory (deterministic, declared, costs per-top regeneration
  of library cores). Under Bluesim-first (section 5) only `.ba` outputs are
  dynamic and the Bluesim link dedupes them by name, which is why that
  ordering removes most of this risk; the explicit-file-list Verilog
  compiles (VCS, Verilator, iverilog) error on duplicate module definitions
  and `-y` only dedupes files not also listed.

### 3.8 Incremental rebuild

`Depend.getGenFs` derives expected outputs from `PPverilog` pragmas
(`src/comp/Depend.hs:188-245`); specializable defs must be excluded (3.3.4).
Specialization outputs themselves are treated like the DPI wrappers:
regenerated whenever the generating package compiles, not tracked by `-u`.

### 3.9 Determinism

`Ord` on `Id`, `FString`, `IType` and `IExpr` is intern-order based
(`src/comp/SpeedyString.hs:22-24`, `src/comp/Id.hs:253-262`,
`src/comp/IType.hs:564-570`, `src/comp/ISyntax.hs:463-512`), so map-ordered
intermediate structures can differ between "child compiled during the parent"
and "child loaded from a `.bo`". This is the same exposure today's
multi-module `gen` loop has. State the invariant as "same result as compiling
the child before the parent in the same process", and add a Phase 0 / 3.11
check that diffs `.v` and `.ba` between a compile that generates a
specialization and one that reuses it from an import.

### 3.10 Diagnostics

`-g` on a specializable def (3.3.5); unresolved type argument (3.4.1);
non-literal static argument, including a parent `parameter` (3.2); genuine
specialization cycle (3.4.3); a `verilog_name` equal to a primitive name
(3.5); a `.ba` flag-profile mismatch at link (3.7); an interface or function
argument on a specializable def (3.2). `showrules`, bluetcl module listings
and `-show-schedule` see specialized modules as ordinary modules named by
`mangle`; `module submods` reports them as user modules.

### 3.11 Tests (`testsuite/bsc.synthesize/specialize/`)

* `PolyIfc.bs`: `mkQueue :: (Bits a sa) => Module (Q a)` marked `verilog {
  specialize }`, instantiated at `Bit 8` and `Bit 32` in one parent: expect
  `mkQueue_Bit8.v`, `mkQueue_Bit32.v`, no `parameter width`.
* BSV `module` syntax (`IsModule m c`) parent and child; a `ModuleContext`
  parent.
* Higher-order uses: `mapM mkArr [4,7]`, `genWithM`, `replicateM`,
  partial application stored in a `let`.
* Static argument interleaved with a `Clock` argument; dynamic static
  argument and parent-`parameter` static argument are errors.
* `param` argument alongside: `parameter [0 : 0] guarded = 1'b0;` in the
  child, `.guarded(1'd1)` at the instantiation (the textual forms the
  parameters tests already pin, `testsuite/bsc.verilog/parameters/`).
* Zero width (`Bit 0`): data ports elided (precedent: `testsuite/bsc.lib/
  fifo/depth_param/` already runs a synthesized zero-width FIFO under both
  backends).
* Nested specializable modules; a self-recursive `mkTree n` over 100 stages;
  a genuine cycle.
* Two specializations sharing one result type in one package; a
  specialization sharing its result type with a monomorphic synthesized
  module.
* Cross-package: `A.bs` defines, `B.bs` and `C.bs` use the same width, with
  and without `C` importing `B`; the determinism diff of 3.9.
* `verilog_name`: def `mkFIFO2` produces `FIFO2_32`.
* Bluesim: `test_c_veri_bsv_multi` on each design with `-keep-fires`; VCD
  scope names via the `vcd_correlation` harness; `-c` byte-identity
  (`check_block_codegen_modules`, `testsuite/config/unix.exp:3366-3400`)
  over the specializations.
* Errors from 3.10; the existing `noinline` polymorphic error still fires.

### 3.12 Estimate and order of work

1500 to 2500 lines of Haskell before tests: the evaluator node and
saturation logic, the round pipeline with symbol-table threading, `IsModule`
handling, pragma/`IdProp`/`.bo` plumbing, `Depend.hs`, the registry and flag
profile. Start with a spike: `ICSpecDef` plus the re-entrant callback on a
two-module example (no GenWrap changes, alias written by hand), which
exercises every evaluation-order edge case before the pipeline work.

## 4. Phase 1b: fidelity prerequisites

These are small compiler and library items that must land before any library
family switches, because without them the switch changes user-visible
behavior.

### 4.1 Schedule fidelity

The BVI imports assert annotations a derived schedule does not reproduce:
`first SB (clear, deq)`, `(notEmpty, notFull) SB (clear, deq, enq)`,
`(clear, deq, enq) SBR clear` (`src/Libraries/Base1/FIFOF_.bsv:158-164`);
CReg's `port_i._read SBR port_{i+1}._write` (`src/Libraries/Base1/
PreludeBSV.bsv:723-760`). With a core whose methods write RWires read by one
update rule, every method pair touches disjoint state and derives CF. At the
bit level that is the same hardware; at the Bluespec level `first CF deq`
lets a rule `deq` and then `first` and read the pre-deq element, which the
BVI forbids. Conversely some BVI annotations are deliberately *looser* than
what hardware suggests (`Counter.bs:35`: `value <> [addA,addB] -- a lie!`);
for Counter the derived result is in fact CF too (`value` reads a register,
`addA` writes an RWire), so that one is reproduced by construction. The
RWire-coupled pairs derive SBR, not SB: `deq SBR full_n` for a loopy FIFO,
which matches the existing `deq SBR i_notFull` (`FIFOF_.bsv:397`).

The BVI also maps two methods with different annotations onto one port
(`notFull` SB enq, `i_notFull` CF enq, both `FULL_N`); a synthesized module
cannot do that (`EPortNamesClashFromMethod`, `src/comp/Error.hs:536`), so
pinning cannot live at the core's boundary. It lives in the non-synthesized
wrapper in `FIFOF_`, which has both methods over one core port:

* **Library mechanism, no compiler change:** `mkRevertingVirtualReg`
  ordering tokens. A method that must be SB another reads a token the other
  writes (`RevertReg`'s own annotation is `read SB write`,
  `src/Libraries/Base1/RevertingVirtualReg.bs`; `RevertReg.v:17` has no
  flop). `first` and `notFull`/`notEmpty` read a token that `deq`, `enq`
  and `clear` write; `i_notFull`/`i_notEmpty` do not. This reproduces every
  SB in the table; SBR (same-rule exclusion) is not expressible this way and
  is the one documented residual.
* **Compiler mechanism, follow-on (8.2):** a `schedule = [...]` override on
  a module's interface, checked "declared at least as restrictive as derived
  unless `unsafe_schedule`", which is also what would let `ConfigReg`,
  `RegFileWCF` and `RevertReg` leave the core.

Exit criterion for Phase 0: the wrapper's exported `VSchedInfo` (via
`-show-schedule` or `bluetcl module schedule`) is identical to the BVI's for
every FIFO variant, and zero `-show-schedule` diffs across the testsuite and
the monorepo when Phase 2 switches.

### 4.2 Port-type fidelity

`savePortType` is `M.insertWith (flip M.union)` and `M.union` is left-biased
(`src/comp/IExpandUtils.hs:1265-1275`): first write wins. GenWrap's generated
wrapper records `Bit n` for every port when the specialization is
instantiated (`saveFieldPortTypes`, `src/comp/GenWrap.hs:2217-2231`), before
the `FIFOF_` wrapper could record the unpacked type the way `mkReg` does
(`src/Libraries/Base1/Prelude.bs:2024-2028`, which works only because
`vMkReg` is a `module verilog` import with no automatic saving). Without a
fix, `wiretypemap` and the `vcd_correlation` goldens (`cells.D_IN :
WireTypes::Cell`) regress to `Bit#(n)`. Fix: make `savePortType` last-wins
(audit the callers), or add `primOverridePortType`. Exit criterion: `bluetcl
module porttypes` / `wiretypemap` on a design using the wrapper shows the
source type.

### 4.3 Backend selection and the A/B knob

Library code can test only `genC`/`genVerilog` (`src/Libraries/Base1/
Prelude.bs:4257-4262`); there is no primitive to read an arbitrary flag, so
"keep the BVI behind a flag" needs one. Add `-prim-impl {verilog,reference}`
and an `Environment` primitive `primReferencePrims :: Bool` (default:
`reference` for Bluesim, `verilog` for the Verilog backend). The library
selects `if genC || primReferencePrims then reference core else BVI import`.
Formal flows that want the reference in Verilog pass `-prim-impl reference`;
production Verilog flows keep `src/Verilog/*.v` until each family's consumers
(CDC/STA constraints, structure tests, name lists) have been updated.

### 4.4 Specialization manifest

bsc writes `<package>.spec.json` (or appends to the `.bo` a readable list)
naming every specialization it generated and its output files, for the build
rules (3.7), the `-c` byte-identity harness and the acceptance tests (7.3).

## 5. Phase 0 and Phase 2: the FIFO family as the pilot

### 5.1 Shape of a reference primitive

Keep the library's two layers (`FIFOF_.bsv` primitive imports, `FIFOF.bs`
guards) and replace only the primitive layer, Bluesim-first (4.3). The
reference core has the *port-level* interface of the Verilog module:
unguarded methods, one method per port group, names fixed by attributes. It
lives in a new package (`src/Libraries/Base1/FIFO_Ref.bs`) that imports
`PreludeBSV` (RWire/PulseWire are defined there, not in `Prelude.bs`) and
`Clocks` (for `isResetAssertedDirect`). In Classic:

```
interface VFIFO2 n =
    enq     :: Bit n -> Action {-# always_ready, prefix = "", arg_names = [D_IN], enable = "ENQ" #-}
    deq     :: Action          {-# always_ready, enable = "DEQ" #-}
    first   :: Bit n           {-# always_ready, result = "D_OUT" #-}
    full_n  :: Bool            {-# always_ready, result = "FULL_N" #-}
    empty_n :: Bool            {-# always_ready, result = "EMPTY_N" #-}
    clear   :: Action          {-# always_ready, enable = "CLR" #-}

{-# verilog mkFIFO2 { specialize, parameter guarded, reset_prefix = "RST", verilog_name = "FIFO2" } #-}
mkFIFO2 :: Bool -> Module (VFIFO2 n)
mkFIFO2 guarded = module
    full_reg  :: Reg Bool <- mkReg True      -- active-low full, as FIFO2.v
    empty_reg :: Reg Bool <- mkReg False
    data0_reg :: Reg (Bit n) <- mkRegU
    data1_reg :: Reg (Bit n) <- mkRegU
    enq_w :: RWire (Bit n) <- mkRWire
    deq_w :: PulseWire <- mkPulseWire
    clr_w :: PulseWire <- mkPulseWire
    in_reset :: Bool <- isResetAssertedDirect
    rules
      "update": when True ==> ... -- transliteration of FIFO2.v:63-66, 92-121, including the
                                  -- illegal-use data path (enq when full overwrites data1_reg)
      "warn":   when guarded && not in_reset && ... ==>
                  $display "Warning: FIFO2: %m -- Enqueuing to a full fifo"
    interface ...
```

Notes on the spelling, all checked against the parser: field pragmas go
after the type (`src/comp/Parser/Classic/CParser.hs:343-388`); `prefix = ""`
with `arg_names = [D_IN]` yields the bare port `D_IN` (`methodArgBaseNames`,
`src/Libraries/Base1/Prelude.bs:4777-4782`); per-field `always_ready` is
honored (`src/comp/GenWrap.hs:937-949`); value methods get no `EN`
(`src/comp/IExpand.hs:1474-1475`); the result type must be `Action`, not
`PrimAction` ("It doesn't seem possible to have a PrimAction field in a
synthesized interface", `Prelude.bs:4706-4707`); the module pragma brace form
and `parameter guarded` are the forms `pVeriGenProps` accepts, and
`reset_prefix` overrides the `RST_N` default (`src/comp/IExpandUtils.hs:
1510-1513`, `src/comp/FlagsDecode.hs:685`). No `CLK_GATE` is emitted unless a
gate pragma asks for it (`src/comp/IExpand.hs:838-840`). Reset polarity uses
the same `BSV_RESET_VALUE`/`BSV_RESET_EDGE` macros as the primitives
(`src/comp/Verilog.hs:110-118`, `src/comp/InlineReg.hs:207-209`).

Expected header of the specialization at 32 bits (port order is by interface
field; choose the field order to approximate the `.v`):

```
module FIFO2_32(CLK, RST, D_IN, ENQ, DEQ, D_OUT, FULL_N, EMPTY_N, CLR);
  parameter [0 : 0] guarded = 1'b0;   // default differs from FIFO2.v (1'b1), see 5.3
  input  CLK; input RST;
  input  [31 : 0] D_IN; input ENQ; input DEQ; input CLR;
  output [31 : 0] D_OUT; output FULL_N; output EMPTY_N;
  reg full_reg; reg empty_reg; reg [31 : 0] data0_reg; reg [31 : 0] data1_reg;
  wire [31 : 0] data0_reg$D_IN; wire data0_reg$EN; ...
```

The outer `vMk2FIFOF` in `FIFOF_.bsv:142-167` becomes a Bluespec wrapper
over `mkFIFO2` that reproduces `FIFOF_`: `notFull`/`i_notFull` both read
`full_n`, ordering tokens pin the SB relations (4.1), `primSavePortType` is
called with the unpacked source type for `D_IN`/`D_OUT` (after 4.2), and the
`valueOf(sa)==0` branch (`FIFOF_.bsv:193-220`) goes away because `FIFO2_0`
elides its data ports.

### 5.2 Phase 0: validate without compiler changes

Monomorphic aliases already synthesize today, so every library-side claim
can be checked before Phase 1:

1. Write `mkFIFO2` as above; add eta-expanded aliases `{-# verilog
   mkFIFO2_32 { parameter guarded } #-} mkFIFO2_32 :: Bool -> Module (VFIFO2
   32); mkFIFO2_32 guarded = mkFIFO2 guarded` for widths 0, 1, 32 (and the
   same for FIFO1, FIFOL1, FIFOL2, SizedFIFO at two depths). The alias must
   be in clause form (binder names drive the `parameter` and port names).
   `verilog_name` does not exist yet, so the bench maps `mkFIFO2_32` to
   `FIFO2`.
2. Diff the generated port list, parameter list and register names against
   the `.v` files; pass `.guarded` explicitly (generated defaults are 0).
3. Lockstep equivalence in the testsuite with Verilator (the harness already
   supports it, `testsuite/config/unix.exp:504-560`): drive `FIFO2 #(32)`
   and `FIFO2_32` with the same random `ENQ/DEQ/CLR/D_IN` stream, including
   illegal uses (enq when full, deq when empty, simultaneous enq and deq when
   full, `FIFO2.v:63`), `CLR`, and mid-stream reset; compare
   `FULL_N/EMPTY_N/D_OUT` every cycle. The oracle is the Verilog; today's
   Bluesim model differs under illegal use (1.4). Formal equivalence (Yosys
   or SymbiYosys) is a welcome optional check, not a testsuite dependency.
4. Bluesim/Verilog co-simulation (`test_c_veri_bsv_multi`) of a design using
   the wrapper, and a VCD name-set comparison of the `FIFO2` scope between
   Bluesim and Verilog with `-keep-fires` on both sides (1.4).
5. `-show-schedule` and `bluetcl module schedule` diff of the wrapper
   against the BVI annotations (4.1), on `testsuite/bsc.lib/fifo` and on
   real monorepo designs, where the schedule and performance deltas live.
6. `bluetcl module porttypes` / `wiretypemap` shows the source type (4.2).

Exit criteria: identical port, parameter and register names where
achievable (5.3), cycle-exact behavior under legal and illegal use, warning
text identical up to the `%m` prefix, identical exported schedule, source
port types preserved.

### 5.3 Fidelity checklist and known deltas

| Item | Status |
|---|---|
| Port names and widths | Identical via attributes; zero-width ports elided (`src/comp/AVerilog.hs:171-172`, `src/comp/AVerilogUtil.hs:969-1070`) |
| Port order in the header | Differs (bsc groups by interface field). bsc uses named connections; only positional external instantiations notice |
| Parameters | `guarded`, `init` identical names via `parameter` args; declared `parameter [0 : 0] guarded = 1'b0;` (default always 0, `src/comp/AVerilog.hs:440-449`) where `FIFO2.v` has `1'b1`; bsc always passes explicit values |
| `width` parameter | Absent; the width is in the module name. Optional: an unused `Integer` `parameter width` fed `valueOf n`, for scripts that read it |
| Module name | `FIFO2_32` instead of `FIFO2`; `FIFO20` becomes `FIFO2_0`. Downstream name lists need a `_\d+` suffix allowance |
| Clock and reset names | `CLK`; `RST` via `reset_prefix`; polarity macros identical |
| Internal registers | FIFO2: all four names achievable (`full_reg`, `empty_reg`, `data0_reg`, `data1_reg`), inlined as `reg` with `$D_IN`/`$EN` wires (`src/comp/BackendNamingConventions.hs:286-291`). Not achievable where the `.v` names the state register after an output port: `FIFO1.v:52` and `FIFOL1.v:57` (`reg D_OUT`), `SizedFIFO.v:67` (`reg D_OUT`, `hasodata`), `RegTwoN.v:29` (`reg Q_OUT`), `McpRegUN.v:27` (`reg get`), `CRegN5.v` (`reg Q_OUT_0`); use `data_out_reg`-style names and document the map per module. `SizedFIFO.v:65` uses a Verilog memory `arr[]`; a `Vector (Reg)` gives flat `arr_0..arr_k` (and k registers in the Bluesim VCD); decide per depth range, `Vector (Reg)` for library depths, memory core beyond |
| Always-block structure | All `RegN`/`RegUN` on one clock share one `always @(posedge CLK)` with the reset branch first (`src/comp/InlineReg.hs:101-125`); `RegA` gets one block per (clock, reset); extra `d0di`-style wires absent |
| Rule signals | `CAN_FIRE_RL_*`/`WILL_FIRE_RL_*` appear with `-keep-fires` in Verilog and Bluesim VCDs; otherwise optimized out in both |
| `initial` blocks | Data registers match (`0xAAAA...` pattern); 1-bit flags get 0 where `FIFO2.v:73-78` sets `full_reg = 1`, visible before reset. The block covers every inlined register and is `translate_off`-wrapped (`src/comp/InlineReg.hs:153-179`) |
| Warnings | Same text with `%m` (Bluesim prints the instance chain without the testbench prefix); must be gated on reset deasserted via `isResetAssertedDirect` because `FIFO2.v:137` only warns when `RST == !BSV_RESET_VALUE`; emitted at the rule's firing, which in Verilog lands at `negedge` system-task time rather than `posedge`, so lines move relative to user `$display` output; Bluesim's text changes from `Warning: <inst> --` to `Warning: FIFO2: %m --`; `FIFOL2.v:138, 143` print `FIFO2:` (reproduce or not, decide); zero-width `FIFO20.v:99, 104` print `FIFO20:` where `FIFO2_0` would print `FIFO2:` |
| Illegal-use data path | Follows the `.v` (data regs load under `CLR`, `data1_reg` overwritten on enq-when-full); Bluesim behavior changes accordingly |
| Reset style macros | `BSV_ASYNC_RESET`, `BSV_RESET_FIFO_HEAD`, `BSV_RESET_FIFO_ARRAY` are Verilog-compile-time switches with no bsc analogue; decide per flow; a bsc flag could select `mkRegA` and reset-on-data in the cores |
| Schedule annotations | Pinned with ordering tokens in the wrapper (4.1); residual: SB where the BVI said SBR for `clear` |
| Path info | Derived; loopy FIFOs get `path (DEQ, FULL_N)` because `full_n` reads `deq_w` (`src/comp/APaths.hs:855-885, 1118-1183`) |
| Port type info | Preserved after 4.2 |
| Bluesim VCD | Module scope with the Verilog port names (they come from `aif_fieldinfo` in the `.ba`, `src/comp/SimPackage.hs:375-400`), `MOD_Reg` flat defs named `full_reg`..., `MOD_Wire` entries for the RWires, fires with `-keep-fires`; today: ports plus `arr_0`, `arr_1` |
| Bluetcl `sim` symbols | Registers and rules instead of `depth`/`level`/`getrange` (`src/bluesim/bs_prim_mod_fifo.h:58-76`); grep MatX bluetcl scripts for `.level`/`getrange` on FIFOs |
| Depth-parameter FIFOs | Stay BVI (3.2) |
| Bluesim speed | Each FIFO becomes a module with rules in the flat schedule; measure (7.3) |

### 5.4 Phase 2 deliverables

1. `src/Libraries/Base1/FIFO_Ref.bs`: `mkFIFO1`, `mkFIFO2`, `mkFIFOL1`,
   `mkFIFOL2`, `mkSizedFIFO` (depth static), `mkSizedFIFOL`, each with
   `verilog_name` equal to the `.v` name, each transliterating the `.v`
   including the illegal-use path.
2. `FIFOF_.bsv`: `vMk1FIFOF`, `vMk2FIFOF`, `vMkSizedNFIFOF` and the loopy
   variants become wrappers that select the reference core under `genC ||
   primReferencePrims` and the BVI import otherwise; the zero-width branches
   disappear on the reference side. `mkDepthParamFIFOF_`/`mkDepthParamLFIFOF_`
   stay BVI and are documented as such.
3. `src/Verilog/FIFO*.v`, `SizedFIFO*.v` stay in the tree, still used by
   default Verilog compiles, and by the lockstep tests forever.
4. Tests from 5.2 become permanent; regold the Bluesim goldens whose FIFO
   warning text changes (eight `.expected` files mention `Warning: FIFO` in
   this tree) and `lambda_calculus.exp` (1.5).

## 6. Phases 3 and 4: the rest of the primitive map

Classification of the 83 `primMap` rows (`src/comp/SimPrimitiveModules.hs:
263-348`). "Core" means native in both backends.

### 6.1 Core

| Primitive | Why |
|---|---|
| `RegN`, `RegUN`, `RegA` | The state element |
| `ConfigRegN/UN/A`, `RevertReg` | Annotation-only differences from `RegN` (`read CF write`; `read SB write` with no flop, `src/Verilog/RevertReg.v:17`). A reference `RevertReg` with a real register adds a flop; keep both core until the compiler override of 8.2 exists. `RevertReg` is also the ordering token 4.1 relies on |
| `CRegN5/UN5/A5` | Expressible (one `mkReg` plus `n` RWires and the chained mux of `CRegN5.v:79-90`, with `n` static), but in Verilog CRegs are *inlined* by default (`src/comp/InlineCReg.hs`, `removeCReg` default on) and the fork's `wiretypemap` knows the inlined names (`src/comp/WireAnalysis.hs:250-270`); a Bluesim-only reference would re-create the Bluesim/Verilog VCD divergence this plan removes. Keep core until one decision is taken for both backends (8.1) |
| `RWire`, `RWire0`, `BypassWire`, `BypassWire0` | The intra-cycle primitive |
| `CrossingRegN/UN/A`, `CrossingBypassWire`/`BypassCrossingWire`, `LatchCrossingReg`, `RegAligned` | The sanctioned unsafe clock-domain read |
| Clock generators and muxes (11 rows) | Create or alter clocks; coupled to `bk_alter_clock`/`bk_trigger_clock_edge` (`src/bluesim/bs_prim_mod_clockgen.h:80`) |
| Reset modules (9 rows) | Reset is a side channel (`src/comp/SimCCBlock.hs:1650-1659`); `ResetToBool` is what `isResetAssertedDirect` uses |
| Memory array: `RegFile`, `RegFileLoad`, `DualPortRam`, `BRAM*Load`, and `BRAM2`/`BRAM2BE` | A dense array is unusable in Bluesim as `Vector (Reg)` at 64K entries; `Load` variants need `$readmemh` (`src/bluesim/bs_prim_mod_regfile.h:284`); `BRAM2.v:41-45` has two write ports in two clock domains sharing one array, which neither a RegFile-style (5R1W) nor a `DualPortRam` (1R1W) core expresses. Keep one memory core with RegFile semantics; `BRAM2*` stays core unless a dual-write core is added. Note `BRAM2.v:41`'s `syn_ramstyle` attribute is lost in any reference |
| `Probe`, `ProbeWire` | Sinks; `Probe` has no `.v` and is dropped by AVerilog (`src/comp/AVerilog.hs:1913`) |
| System tasks | Runtime services |

### 6.2 Phase 3: register-like primitives (Bluespec over Reg and RWire)

| Primitive | Reference | Notes |
|---|---|---|
| `Counter` (`src/Libraries/Base1/Counter.bs:24, 65`, `Cntrs.bsv:62`) | `mkReg init` plus RWires for `ADDA/ADDB/SETC/SETF`, one rule with the priority of `Counter.v:59-62` | `init` as `parameter`; derived `value CF addA` reproduces the BVI (4.1); `WireAnalysis.hs:281` matches `VName "Counter"` exactly and emits the `q_state` alias Bluesim writes (`bs_prim_mod_counter.h:172, 190`), so `Counter_8` needs that match generalized (7.1) |
| `RegTwoN/UN/A` (`src/Libraries/Base2/RegTwo.bs`) | Reg plus two write RWires with the `.v` priority | `RegTwoN.v:29` names the flop `Q_OUT`; use another name |
| `McpRegUN` (`src/Libraries/Base2/Mcp.bs:417`) | shift register of `delay` stages | `delay` static; `McpRegUN.v:27` names the flop `get` |
| `RegFile` wrapper (`src/Libraries/Base1/RegFile.bs:52-192`) | thin wrapper over the memory core | `WCF` variant is annotation-only; needs 8.2 to leave the core |
| `BRAM1`, `BRAM1BE` (`src/Libraries/Base2/BRAMCore.bsv:148-260`) | memory core plus output registers, WRITE-FIRST (`BRAM1.v`), `EN`-gated read register, `PIPELINED` static, byte enables as a vector of writes | `*Load` variants stay core until 8.3 |

### 6.3 Phase 4: synchronizers (Bluesim side only)

`SyncBit`, `SyncBit05/1/15`, `SyncPulse`, `SyncHandshake`, `SyncRegister`,
`SyncFIFO/0/1/10`, `SyncFIFOLevel/0` (`src/Libraries/Base1/Clocks.bsv:
724-1375`, `FIFOLevel.bsv:879-961`): registers `clocked_by` the two domains
with the unsafe crossing through `CrossingRegN`, gray-code pointers as in
`SyncFIFO.v`, `depth` static and checked at elaboration (replacing the
`$finish` in `SyncFIFO.v:260`). Three constraints the first revision
missed: every `Sync*.v` uses `always @(posedge CLK or BSV_RESET_EDGE RST)`
unconditionally (`SyncBit.v:44, 59`, `SyncRegister.v:55, 74`, `SyncFIFO.v:
112-157`), so the references must use `mkRegA`; `SyncRegister.v:74-76` and
`SyncFIFO.v:89` reset destination-domain registers from the source reset
(`dRST = sRST`), which bsc rejects (`EResetClocks`, `src/comp/Error.hs:
3425-3440`), so either a core unsafe reset-crossing primitive is added or
the reference takes a `dRST` port (a port-list delta); and the hand-written
`Sync*.v` register names (`sSyncReg`, `dSyncReg1`, `dSyncReg2`,
`sGEnqPtr`) are what CDC lint waivers and `set_false_path`/`set_max_delay`
constraints match on, so the Verilog side of this family stays hand-written
indefinitely and only the Bluesim side switches. Equivalence here is
cycle-level co-simulation with both clocks driven from one Verilator
testbench. Bluesim already supports MCD rules (`src/comp/SimExpand.hs:
316-334`).

### 6.4 Leave as is

`OVLAssertions` (external library), inout and tristate modules (Bluesim does
not support them), `ConstrainedRandom`, `SPSRAM`/`DPSRAM` (already Bluespec
under `genC`), `JoinClock` (already unsupported in Bluesim), and the
`src/Verilog/Makefile` entries without `primMap` rows (`SampleReg.v`,
`SyncWire.v`, `ResetInverter.v`, `Probe{Capture,Hook,Mux,Trigger,Value}.v`).

### 6.5 Depth-parameter FIFOs

`mkDepthParamFIFO`/`mkDepthParamLFIFO` (FIFO.bs:82-93, FIFOF.bs:278-313)
exist so a parent Verilog `parameter` can set the depth. They cannot be
specialized (3.2). Either keep them as BVI imports of `SizedFIFO.v`
indefinitely (which keeps `SizedFIFO`/`SizedFIFOL` in `primMap` and the
`Fifo` C++ class alive for Bluesim) or deprecate them. Decide with their
users before Phase 5 touches the FIFO rows.

## 7. Phase 5: Bluesim removal and cleanup

### 7.1 Name-keyed code to change

For each family after its reference lands and the library no longer emits
the BVI name under Bluesim, update every table that matches primitive names,
not only `primMap`:

* `src/comp/SimPrimitiveModules.hs:263-348` rows and the
  `getPrimDomainInfo`/`isFIFO`/`isCReg`/`is*PortBRAM` cases (`:390-687`);
  `SimCCBlock.hs:536`; `SimMakeCBlocks.hs:634, 728, 937`.
* `src/comp/BackendNamingConventions.hs:470-515` (`isFIFO`, `isFIFO0`,
  `isSyncReg`) used by `bluetcl.hs:3707-3750` (`adjustPrimFields`, which
  today maps the FIFO ports back onto `FIFOF`'s `notFull`/`notEmpty`; for a
  reference core either teach it the core's method names or keep
  `notFull`/`notEmpty` as the core method names) and `showrules.hs:
  1494-1524` (FIFO/Reg/RWire/RegFile signal mapping).
* `src/comp/WireAnalysis.hs:117, 257, 281` (CReg and `Counter` exact-name
  matches); `bluetcl.hs:1213-1214` (`wiretypemap` returns empty for
  primitives).
* `src/comp/LambdaCalcUtil.hs:1257-1322`.
* `testsuite/config/unix.exp:638` (`verilator_unsupported_mods`).

Match specializations by a base-name property (`verilog_name` or
`IdPSpecialization`) rather than exact `vName`, so that MatX's correlation
and `showrules` flows do not lose hits silently. Add a grep gate: no
remaining string match of a removed primitive name in `src/comp` or
`testsuite/config`.

### 7.2 Deletion

Then delete the C++ (`src/bluesim/bs_prim_mod_fifo.h`, `prim_mod_fifo.cxx`,
`_counter`, `_synchronizers`, most of `_reg.h` except `MOD_Reg`,
`MOD_ConfigReg`, `MOD_CReg` while CReg is core, `_regfile.h`/`_bram.h` down
to the memory core), and keep the stale-`.bo` failure path: a `.bo` that still
instantiates a removed BVI name fails with `EBSimForeignImport`
(`src/comp/ABinUtil.hs:274-285`). Expected end state of `primMap`: Reg family
and Crossing variants, ConfigReg, RevertReg, CReg (pending 8.1), wires,
memory core, `BRAM2*`, clocks, resets, probes: roughly 45 of 83 rows. Remove
the corresponding `src/Verilog/*.v` from `src/Verilog/Makefile` only for
families whose Verilog side has also switched (8.1); the lockstep tests keep
copies.

### 7.3 Acceptance tests before deleting any Bluesim C++ (per family)

1. Lockstep Verilator equivalence of reference vs hand-written `.v` at widths
   {0, 1, 2, 7, 8, 32, 33, 64, 65, 128} and depths {2, 3, 4, 8, 16}, both
   `guarded` values, illegal use, `CLR`, mid-stream reset, and every `BSV_*`
   macro combination the MatX flow uses.
2. Full bsc testsuite under `test_c_veri_bsv_multi` with Bluesim output
   identical to Verilog output except a reviewed list of warning-text and
   ordering changes; the separate `.v.out.expected` variants for FIFO tests
   should become unnecessary.
3. `-c` byte-identity (`check_block_codegen_modules`) over every
   specialization, discovered from the manifest (4.4), not a hand list.
4. VCD scope and signal-name-set equality between Bluesim and Verilog for
   each reference module (extend `testsuite/bsc.bluetcl/vcd_correlation`,
   with `-keep-fires`), and `bluetcl sim ls/cd/lookup` plus `showrules` on a
   design with reference FIFOs.
5. Zero `-show-schedule` diffs across the testsuite and the monorepo with
   4.1 in place; any delta is a reviewed, named exception.
6. Bluesim throughput and C++ build time on the most FIFO-heavy monorepo
   `_bluesim` targets within an agreed budget of baseline (say 10 percent);
   bsc wall time on the full monorepo build within an agreed budget (say 5
   percent), with the count of specializations compiled reported under `-v`.
7. Monorepo: all `bs_test` backends green with the manifest-driven outputs;
   a test where two packages demand the same specialization links in Bluesim
   and, once the Verilog side switches, compiles in iverilog, VCS and
   Verilator without duplicate-module errors.
8. Stale `.bo` instantiating a removed primitive fails with
   `EBSimForeignImport`, tested.
9. Formal: LambdaCalc/SAL dumps still produced for designs using FIFOs; the
   MatX formal flow composes per-width modules.
10. Negative compiler tests from 3.11, the `ISimplify` guard, the
    canonical-flags determinism check.

## 8. Follow-on work

### 8.1 Verilog-side switch per family

With `-prim-impl` (4.3) available per design, each family's Verilog default
flips only when its consumers are ready: name lists accept `_<n>` suffixes,
structure tests are regolded, `wiretypemap`/`vcd_correlation` goldens are
reviewed, and for CReg the inline-versus-boundary decision is taken for both
backends at once (either teach `InlineCReg` to inline a synthesized
`CReg_*`, or accept the structural change). Synchronizers stay hand-written
in Verilog (6.3).

### 8.2 Compiler schedule override

`schedule = [...]` on a module's interface, applied where the wrapper's
`VSchedInfo` is built (`src/comp/GenWrap.hs:1463-1536`) and in the
non-synthesized wrapper case as an annotation the scheduler honors: declared
at least as restrictive as derived is accepted; a relaxation needs
`unsafe_schedule`. Lets `ConfigReg`, `RegFileWCF`, `RevertReg` leave the
core, replaces the ordering tokens of 4.1 where SBR exactness matters, and
makes the Counter "lie" explicit. Comparison function in
`src/comp/SchedInfo.hs`, treating SBR as the derived relation for
RWire-coupled method pairs.

### 8.3 Memory file loading

`RegFileLoad`/`BRAM*Load` need `$readmemh`/`$readmemb` at start. A
`primReadMemFile` system-task foreign function usable from a reference
module's initial rule (Verilog: `$readmemh` in an `initial` block; Bluesim:
`read_mem_file`, `src/bluesim/bs_mem_file.h`) moves the array out of C++ and
keeps one runtime hook.

### 8.4 Parameterized shells (cosmetic)

If a consumer needs a module literally named `FIFO2` with `parameter width`,
a link-time tool can wrap the specializations present in a design in a
`generate case (width)` shell. Should not gate anything.

### 8.5 Bluesim performance

Measure after Phase 2 (7.3.6). If the flat-schedule cost of reference FIFOs
matters, the mitigation is in the Bluesim backend (inlining small leaf
modules into the parent's schedule), not in the primitives.

### 8.6 Instantiation-site pragma and upstreaming

`(* synthesize *)` on an instantiation (#921) is the same node and callback
triggered from `PrimModuleBind`. Phase 1 is upstreamable independently of the
library switch; note that `IExpand.hs` is the most fork-modified file (lazy
pack/unpack, Integer parameters, ATF cache), so the upstream version is
written against upstream `IExpand` and simply lacks the pack/unpack
cancellation nicety. Designing for the re-entrant form matches quark17's
stated preference and improves acceptance odds.

## 9. Risks and open questions

1. **Compile time.** Each specialization is a full per-module pipeline run
   (round pipeline plus `genModule`) inside the parent's elaboration, and
   MatX runs bsc twice per library (Verilog and Bluesim). Gate Phase 2 on the
   wall-time budget of 7.3.6; the manifest reports the count.
2. **Flag-dependent contents** across packages (3.7): canonical profile for
   library specializations, error on mismatch.
3. **Schedule deltas** in existing designs (4.1): tokens plus the zero-diff
   exit criterion; SBR residual documented.
4. **Hermetic builds** (3.7): manifest and directory outputs or keys-only
   registry; decide before Phase 2. Bluesim-first keeps only `.ba` dynamic.
5. **CReg in Verilog** (6.1, 8.1): one decision for both backends.
6. **Bluesim speed** (8.5).
7. **Name collisions.** A user module named `FIFO2_32` collides with a
   specialization; the registry errors on a clash with a non-specialization
   of the same name. A `verilog_name` equal to a primitive name is rejected
   while the name tables exist (3.5).
8. **Evaluation-order edge cases** are where Phase 1's risk concentrates
   (higher-order module use, heaped partial applications, `ISimplify`
   inlining, self-key, cycles); the spike in 3.12 is there to surface them
   before the pipeline work.
9. **Determinism** (3.9): same-process invariant, not bit-identity with a
   fresh compile.
10. **Monorepo golden churn** is larger than bsc testsuite churn: Verilog
    structure tests, sim-log goldens (warning text and `negedge` timing),
    `-show-schedule` dumps. Phase 0 on real designs sizes it.
11. **Depth-parameter FIFOs** (6.5) block full removal of the `Fifo` C++
    class and `SizedFIFO.v` unless deprecated.
12. **Not verified by execution.** No bsc binary was available while writing
    this; the claims were checked by reading the source and by adversarial
    review against it (Appendix B). Phase 0 and 3.11 are the executable
    checks.

## Appendix A. Port and parameter targets for the replaceable primitives

Headers taken from `src/Verilog/*.v`. A reference implementation must
reproduce the port names and the parameters that are *values*; parameters
that size structure become part of the specialized module name (3.5).

| Verilog module | Ports | Value parameters (stay `parameter`) | Structural parameters (become name suffix) |
|---|---|---|---|
| `FIFO1`, `FIFO2` | `CLK, RST, D_IN, ENQ, FULL_N, D_OUT, DEQ, EMPTY_N, CLR` | `guarded` | `width` |
| `FIFO10`, `FIFO20` | same minus `D_IN, D_OUT` | `guarded` | (width 0 specialization) |
| `FIFOL1`, `FIFOL2` (`FIFOL10`, `FIFOL20`) | as `FIFO1`; `FULL_N = ... \|\| DEQ` combinational (`FIFOL1.v:71`, `FIFOL2.v:57`) | none | `width` |
| `SizedFIFO`, `SizedFIFOL` (`SizedFIFO0`, `SizedFIFOL0`) | as `FIFO1` | `guarded` (`SizedFIFO` only) | `p1width`, `p2depth` (`p3cntr_width` derived) |
| `Counter` | `CLK, RST, Q_OUT, DATA_A, ADDA, DATA_B, ADDB, DATA_C, SETC, DATA_F, SETF` | `init` | `width` |
| `CRegN5` | `CLK, RST, Q_OUT_i, EN_i, D_IN_i` for i in 0..4 | `init` | `width` (and port count, today fixed at 5) |
| `RegTwoN` | `CLK, RST, Q_OUT, D_INA, ENA, D_INB, ENB` | `init` | `width` |
| `RevertReg` | `CLK, Q_OUT, D_IN, EN` | `init` | `width` |
| `McpRegUN` | `CLK, RST, SET, val, get` | none | `width`, `delay` |
| `RegFile` | `CLK, ADDR_IN, D_IN, WE, ADDR_i, D_OUT_i` for i in 1..5 | none (`lo`/`hi` size `arr[lo:hi]`, `RegFile.v:37`) | `addr_width`, `data_width`, `lo`, `hi` (core) |
| `BRAM1` / `BRAM2` | `CLK, EN, WE, ADDR, DI, DO` / `CLKA..DOA, CLKB..DOB` | none | `PIPELINED`, `ADDR_WIDTH`, `DATA_WIDTH`, `MEMSIZE` |
| `BRAM2BE` | as `BRAM2` | none | plus `CHUNKSIZE`, `WE_WIDTH` |
| `SyncBit` (`05/1/15`) | `sCLK, sRST, dCLK, sEN, sD_IN, dD_OUT` | `init` | none |
| `SyncRegister` | `sCLK, sRST, dCLK, sEN, sRDY, sD_IN, dD_OUT` | `init` | `width` |
| `SyncFIFO` (`0/1/10`), `SyncFIFOLevel` (`0`) | `sCLK, sRST, dCLK, sENQ, sD_IN, sFULL_N, dDEQ, dD_OUT, dEMPTY_N` (+ level ports) | none | `dataWidth`, `depth`, `indxWidth` (derived) |
| `SyncHandshake` | `sCLK, sRST, dCLK, sEN, sRDY, dPulse` | `init`, `delayreturn` | none |
| `SyncPulse` | `sCLK, sRST, dCLK, sEN, dPulse` | none | none |
| `DualPortRam` | `CLK, WE, WADDR, DIN, RADDR, DOUT` | none | `addrWidth`, `dataWidth` (core) |
| `ProbeWire` | `OUT, IN` | none | `size` |

Clock and reset argument ports: Classic has no `clock_osc`/`reset_port`/
`arg_port` spellings (`src/comp/Parser/Classic/CParser.hs:640-660`); a clock
argument `sCLK` becomes port `CLK_sCLK` by default (`makePrefixArgId`,
`src/comp/IExpandUtils.hs:1538-1545`). Use `clock_prefix = ""` and
`reset_prefix = ""` with argument names `sCLK`, `dCLK`, `sRST`: `join2ids`
drops the empty prefix (`src/comp/Id.hs:441-452`). BSV can also use the
`port`/`osc`/`reset` argument attributes.

## Appendix B. How this plan was checked

The findings in sections 1 and 3 to 7 come from eight parallel read-throughs
of the compiler (GenWrap, driver, IExpand, Verilog backend, Bluesim backend,
libraries, documentation and upstream history, type machinery), a
completeness pass over them, and then an adversarial pass in which seven
reviewers tried to refute 21 load-bearing claims against the source and
three reviewers critiqued the resulting plan from compiler, library and
delivery perspectives. Of the 21 claims, 3 were confirmed as stated and 18
were partially correct; every correction is folded into this revision (the
evaluator node instead of a side condition; `IsModule` handling; the
self-key; the alias clause form; the round pipeline and symbol-table
threading; `EBSimForeignImport` keyed on `avi_user_import`; the first-wins
`savePortType`; `PrimAction` versus `Action`; `parameter [0 : 0] ... =
1'b0`; `-keep-fires` for Bluesim VCD content; the `Sync*.v` reset
constraints; `BRAM2`'s dual write ports; the depth-parameter FIFOs; the
name-keyed tables beyond `primMap`; the determinism caveat; the `-g`
pragma persistence; the LambdaCalc golden). Nothing was executed.
