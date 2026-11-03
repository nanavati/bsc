# Handoff prompt: emit parameterized Verilog from size-polymorphic `synthesize` modules

This file is a prompt. Give it verbatim to an implementing agent. It is
self-contained. It describes the *parameterized output* design: one
Verilog module with `parameter width`, generated once. (The sibling file
`specialize_synthesis_handoff.md` describes a different design, one
monomorphic module per instantiation; do not mix the two.)

---

Implement size-polymorphic synthesis in the Bluespec compiler (bsc): a
module marked `synthesize` and `parameterized` whose only polymorphism is in
numeric type variables is synthesized **once**, when its own package is
compiled, into a Verilog module whose numeric type variables become Verilog
`parameter`s, and importers instantiate it with `#(.width(32))` exactly as
today's hand-written `src/Verilog/FIFO2.v` is instantiated through `import
"BVI"`.

## WHERE

Repository: the MatX fork of bsc, `matx-inc/bsc`, not upstream
`B-Lang-org/bsc`. This prompt was written against `matx-inc/bsc` branch
`main` at commit `99677cb` (2026-10-02, the `release-2026.07.rc8` lineage;
`.bo`/`.ba` format tags `bsc-bo-20260715-6` / `bsc-ba-20260715-6`). If you
are told to target the `release-frozen-A0` line instead (`fdd13b8`,
2026-10-20), everything below applies with one relocation: the driver
`src/comp/bsc.hs` lives at `src/comp/app/bsc.hs` there, the format tags are
`-14`, and binary tag numbers must be re-derived from that tree. Work on a
fresh branch off the chosen commit.

FIRST read `DEVELOP.md`, `INSTALL.md` (`make install-src` builds into
`inst/`), `testsuite/README.md` (`make localcheck` in a test subdirectory),
and `doc/design/size_polymorphic_synthesis.md` sections 1.3 and 2 for the
background on why this is the expensive design. Line numbers in this prompt
are from `99677cb` and may have drifted; search by the function names.

## WHY

bsc rejects `synthesize` on any module with a type variable or proviso
(`chkType` in `src/comp/GenWrap.hs`: "Its interface is polymorphic.", "It
has a proviso.", T0043), because elaboration is a concrete-width partial
evaluator: `type ASize = Integer` (`src/comp/ASyntax.hs`), `PrimValueOf` on
a non-literal size is an internal error (`src/comp/IExpand.hs`), every
back-end pass computes with literal widths. The only size-polymorphic
synthesis boundaries today are hand-written Verilog primitives
(`src/Verilog/FIFO2.v`: `parameter width = 1; input [width - 1 : 0] D_IN;
reg [width - 1 : 0] data0_reg;`) imported through `import "BVI"` /
`module verilog` with `parameter width = valueOf(sa)`, plus a parallel
hand-written C++ model for Bluesim.

The goal is to replace those hand-written primitives with reference
Bluespec implementations that generate the *same kind* of artifact: a single
`FIFO2.v` with `parameter width`, so that the Verilog library, the formal
flows that read it, and downstream tools that key on `FIFO2 #(.width(32))`
keep working unchanged. The original bsc authors left dormant hooks for
exactly this (`imod_type_args` "If we supported generation of modules with
numeric type variables, they would be in this list", `apkg_size_params`,
AState's size-parameter inputs, `ENotKNum` "Only size polymorphism allowed
in code generation", GenWrap's `IfcTRec.rec_numargs` "Until we support
synthesis of size-parameterized modules"). This task revives that path.

Bluesim consumes the same artifact. The parameterized module also gets a
`.ba` whose sizes are symbolic, and Bluesim's link step instantiates it per
distinct parameter set (the way a Verilog simulator elaborates a
`parameter`ized module): `simExpand` binds `width = 32` from the parent's
instance arguments, substitutes into a copy of the module, folds, and
registers a monomorphic module for code generation. One C++ class per width
is exactly the shape the hand-written primitives have today
(`MOD_Fifo<tUInt32>`), so this is the mechanism by which reference Bluespec
implementations will *replace* the Bluesim primitive library: same import
name, same parameters, `primMap` row deleted, `FIFO2.ba` and `FIFO2.v`
shipped together. No backend selection by `genC`/`genVerilog` anywhere: one
`.bo`, one `.ba`, one `.v`, and the wrapper is identical for both backends.

## WHAT (what done looks like)

In Classic syntax (the Prelude dialect):

```
interface VPass width =
    put :: Bit width -> Action   {-# always_ready, prefix = "", arg_names = [D_IN], enable = "EN" #-}
    get :: Bit width             {-# always_ready, result = "Q_OUT" #-}

{-# verilog mkPass { parameterized } #-}
mkPass :: Module (VPass width)
mkPass = module
    r :: Reg (Bit width) <- mkRegU
    interface
        put x = r := x
        get = r
```

(BSV: `(* synthesize, parameterized *)`.) `bsc -verilog` on that package
produces `mkPass.v`:

```
module mkPass(CLK, RST_N, D_IN, EN, Q_OUT);
  parameter width = 1;
  input  CLK; input RST_N;
  input  [width - 1 : 0] D_IN; input EN;
  output [width - 1 : 0] Q_OUT;
  reg [width - 1 : 0] r; wire [width - 1 : 0] r$D_IN; wire r$EN;
  ...
```

A parent that does `a :: VPass 8 <- mkPass; b :: VPass 32 <- mkPass`
produces `mkPass #(.width(32'd8)) a(...)` and `mkPass #(.width(32'd32))
b(...)` and compiles and simulates with Verilator against `mkPass.v`; under
`bsc -sim` the same parent links against `mkPass.ba` (symbolic sizes), and
the Bluesim link produces two generated classes, `mkPass__width8` and
`mkPass__width32`, with `a` and `b` as instances of them, VCD scopes `a`
and `b` showing `r` at 8 and 32 bits, and Bluetcl `sim ls` navigating into
them. A second link of the same design produces byte-identical C++ for the
instantiated modules (the `-c` byte-identity harness passes). The reference
cores for FIFO1, FIFO2, FIFOL1, FIFOL2 and Counter (the hand-written
`src/Verilog/*.v` transliterated into Bluespec, see the fidelity table in
`doc/design/size_polymorphic_synthesis.md` section 5.3) generate Verilog
with the same ports, the same `parameter` list (plus `width`), the same
register names, and pass a Verilator lockstep test against the hand-written
files at widths 1, 7, 8, 32, 33, 64, 65, 128. A module that uses a size
parameter structurally (a `Vector width`, a loop to `valueOf width`, an `if`
on `valueOf width == 3` that no proviso decides) is rejected with a clear
error at the offending position. A module polymorphic in a non-numeric type
variable is rejected with T0041. Monomorphic `synthesize` modules and every
existing test are byte-identical before and after.

## CURRENT STATE (what exists, by function name)

Dormant hooks. `imod_type_args :: [(Id, IKind)]` in `src/comp/ISyntax.hs`
is returned by `iExpandModuleDef` as `iks` (hard-coded `[]` with the comment
"this was to allow code-gen of modules with numeric parameters, but we
don't support that", `src/comp/IExpand.hs`), stored in the `IModule`, and
forwarded by AConv to `apkg_size_params`; `ISyntaxCheck.tCheckIModule`
already binds those kinds, so a free `ITVar width` type-checks under
`-check` once it is listed. AState turns each size param into a parameter
input `(p, aTNat)` ("XXX size parameters are bit-32?") and AVerilog emits
`aspkg_parameters` as `VAParameter` with range and default 0, and accepts a
parent parameter as a constant when checking a submodule's instantiation
parameters (`isConstVE parent_ps`); `ASParam` prints as `VEVar`.
`APaths.aPathsPreSched` internal-errors "size parameters not supported"
when the list is non-empty. `ENotKNum` (T0041) is defined in
`src/comp/Error.hs` and raised nowhere. `extractModuleArgs` errors on any
leading `ILAM` regardless of kind (`reportNonSynthTypeInModuleArg`, which
internal-errors "unexplained module with type parameter" when no `Bits`
dictionary lambda follows), and an `ILAM` with no type argument is WHNF in
`evalAp'`, so a leading numeric `ILAM` does reach it intact.

Evaluator. Numeric type functions are folded only by the `ITAp` smart
constructor `mkITAp` when both arguments are `ITNum` (`src/comp/IType.hs`,
`opNumT` in `src/comp/TypeOps.hs`); `fullTypeNormalizer` (in
`src/comp/IExpandUtils.hs`) leaves `ITVar` unchanged (its local `canNorm`);
`tSubst` never reduces. `TAdd`/`TLog` are
`TIabstract` constructors, so `TAdd width 1` stays as an interned
application; `TAdd width 1` and `TAdd 1 width` are different interned types.
`PrimValueOf` folds only `[T (ITNum n), _]` and internal-errors otherwise.
Strict bit primitives fold only when `all isIntLit` holds over type and
value args (`isIntLit (T (ITNum _)) = True`), otherwise they fall to the
residual `bldAp'` path; `doPrimOp` (`src/comp/IPrims.hs`) silently drops
non-`ITNum` type args (`tints = [i | ITNum i <- ts]`) and then fails its
arity patterns, so symbolic-width folding is prevented by accident;
`ITransform.iTrAp` calls `doPrimOp` with unfiltered type args.
`PrimIntegerToBit`/`UIntBits`/`IntBits` have clauses only for `[T (ITNum
k), E e]`; they are not in `strictPrim`, so a non-literal type argument
falls to `conAp'`'s catch-all internal error. `PrimZeroExt` rewrites to
`PrimConcat` with a zero literal built as `iMkLitAt ... (aitBit t) 0`, which
already yields an `ICInt` whose type is `Bit (ITVar k)` when `t` is
symbolic; `PrimTrunc` rewrites to `PrimSelect`. Integer primitives
(`integerPrim`) fold only on literal operands and otherwise `nfError`
(`ENoNF`, "Compile time expression did not evaluate"); the commented-out
`isIConParam` branches show symbolic Integer operands were once
considered. `doIf` selects on `ICInt 0/1`, else builds a residual `PrimIf`;
a residual `PrimIf` at `Module` type is `EDynamicModule`, at `Integer` type
`evalInteger` fails. `PrimTypeOf`, `PrimPrintType` and `doBuildUndefined`
(through `evalCExpr`) call `iToCT`, which internal-errors on `ITVar`.
`chkStateVarTypes` internal-errors on any free type variable in a
state-variable type. `bitTupleSizes` treats a non-`ITNum` `Bit` as width
0. `ICLazyPack`/`ICLazyUnpack` hold `pack`/`unpack` at symbolic widths
(the hold guards test `tn /= ITNum 0`, `tn /= ITNum 1`). The fork's
`handleInt` re-types an `Integer` `ICModParam` to `ICModParam (itBitN k)`
("no range check is possible on a symbolic value"), `Params.isConstIExpr`
accepts `ICModParam`, and AConv maps it to `ASParam`: a symbolic *value*
path already exists; `ICModParam` carries only its type, not the
originating type variable.

Numeric-predicate solver. `SATPred.solvePred :: SATPredState -> [Pred] ->
Pred -> IO (Maybe Pred, SATPredState)` (`src/comp/SATPred.hs`) over
`Pred2Yices`/`Pred2STP`, handling `NumEq`, `Add`, `Mul`, `Max`, `Min`,
`Div`, `Log` with 32-bit bit-vectors and overflow side conditions; `Just p`
means given-and-p satisfiable and given-and-not-p unsatisfiable; `Nothing`
conflates "refuted" and "unknown". `TCMisc.batchSolveNumericPreds` is the
typechecker driver (one solver session per atomic IO block; see the
`SATPred.hs` header comment on why). The evaluator has no access to a
module's provisos today: `ILAM` carries only kinds.

GenWrap. `chkType` rejects provisos and type variables; `fixupPolyModType`
ties a single `IsModule` predicate. The import-BVI path (`fixVerilogIfc` /
`fixCModuleVerilog`) is the model for a size-polymorphic boundary: it folds
`procType` over all field types, mints an interface parameter `n_#` per
polymorphic type with a `Bits ty sn_#` proviso and a `rec_typemap` entry
`(ty, Bit n_#)`, sets `rec_kind = Kfun KNum ...` and `rec_numargs`, and
`genTDef`/`genIfc` declare the flattened struct with those parameters;
`genIfcFieldFN` rewrites leaf types through `rec_typemap`. `mkTo_` and
`mkFrom_` only have equations for `rec_numargs = []` and `rec_typemap =
[]` (internal error otherwise); `mkGeneric` (called from `mkInstances`) is
unrestricted but builds the flattened type as `cTCon flat_id` unapplied;
all three are mapped over the synthesized records only. `mkNewModDef` types
the inner def as `tmod (cTCon tyId)`; `mkDef` builds the wrapper `CDef i
cqt [clause]` with the def's original `CQType` (so it is polymorphic for
free) around `liftModule (xWrapperModuleVerilog fmod pps (CLit (LString
(getIdBaseString i))) wire_info arg_exprs ...)`, where `wire_info` is the
elaborated `imod_external_wires` and `xCmoduleVerilog` zips its `VArgInfo`
list with the wrapper's argument expressions. Classic `vMkReg` declares
`module verilog "RegN" (("width",valueOf n), ("init",v)) "CLK" "RST"
{...}` (`src/Libraries/Base1/Prelude.bs`); BSV `vMk2FIFOF` declares
`parameter width = valueOf(sa)` (`src/Libraries/Base1/FIFOF_.bsv`). Classic
`foreign` functions already name Verilog instance parameters after their
numeric type variables in quantification order (`MakeSymTab.chkTopDef`
`tvnames`, numeric-only provisos allowed and erased by IConv's
`foreignPredCount`; `src/Libraries/Base1/Fork.bs` against
`src/Verilog/Fork.v` `parameter iw = 1; parameter ow = 2;`).

Back end. `ATBit { atb_size :: ASize }` with `type ASize = Integer`;
`aSize` is a method of `class ATypeC a where aSize :: a -> Integer` in
`src/comp/ASyntaxUtil.hs` with instances for `AType` (`ATBit s -> s`) and
`AExpr`. `AType` derives `Ord` (and `Eq`, `Show`) and is a container key
(`CSEMap` in AConv, maps keyed on `(AExpr, AType)` in AVeriQuirks and
ANoInline, `Set AExpr` in AUses); `AExpr`, `ADef`, `AAction`, `AClock`,
`AReset`, `AInout` derive `Ord` too. `aTypeConv` (`src/comp/AConv.hs`) converts
only `Bit (ITNum n)` and otherwise falls to an `ATAbstract` case or an
internal error. Pass order under Verilog (`src/comp/bsc.hs`): `aState`,
`aInlineWires`, `aInlineCReg`, `aRenameIO`, `aDropDefs`, `aOpt`,
`aSynthesize`, `aVeriQuirks`, `finalCleanup`, `getIOProps`, `aVerilog`;
`ACheck` runs after each. Width-computing sites (grep counts of `ATBit` /
`aSize`): AOpt 29/8, AExpr2Yices 28, AExpr2STP 28, ASyntax 26, AVeriQuirks
22, AConv 18, Synthesize 15, SimCCBlock 10/45, AVerilogUtil 9/16, ACheck 8,
AState 6, ForeignFunctions 15, SAL 11, APrims 11; zero in ADropDefs,
ARenameIO, ACleanup, VFinalCleanup, APaths, ANoInline, ATaskSplice,
DPIWrappers, GenABin, AAddSchedAssumps. The Verilog AST already allows
symbolic ranges (`type VRange = (VExpr, VExpr)`, `VEOp`, `VEVar`,
`VERepeat`, `VEFctCall`, `VEIf`; `ppOp` parenthesizes by fixity) and the
hand-built `Mux_n` primitives in `src/comp/VPrims.hs` are the one existing
symbolic-range emitter (`VAParameter viWidth Nothing (VEConst 1)` printed
as `parameter width = 1;`, ports ranged `(width - 1, 0)`). `vSize` always
emits `VEConst (n-1)`; `VEWConst` and `VEUnknown` need an `Integer` width
(`createVEWConstString`, the `aaaa` pattern from `src/comp/IntegerUtil.hs`).
`InlineReg.mkRegInstInfo` requires the register width to be an `ASInt`
literal; `InlineWires`/`InlineCReg` likewise read the width from
`avi_iargs`. Scheduling reaches the solvers only through `DisjointTest` →
`AExpr2STP`/`AExpr2Yices`, which create bit-vector sorts from literal widths
and have `addUnknownExpr mty e width` for anything unmodelled; `Nothing` or
`Just False` from the solver is treated as a conflict by `ASchedule`
(conservative). `BinData`'s `Bin AType` writes `ATBit sz` as an `Integer`.

Driver, link, library. `generating = backend flags /= Nothing`; GenWrap
wraps when `generating && PPverilog`; `genModuleVerilog` runs only under
`backend == Just Verilog`; `writeABin` only under `genABin` (`-sim` forces
it, `-elab` enables it). `vLink` walks `.ba` hierarchy with
`getABIHierarchy` and falls back to the `.v` list if the walk fails
("Until we allow re-generation of Verilog files, the module .ba files are
unused"); `followABMIHierarchy` partitions instances on `avi_user_import`:
user imports are leaves and never looked up, native submodules need
`<name>.ba` (`EMissingABinModFile`), and Bluesim errors on a user import
that is not a primitive (`EBSimForeignImport`). The `.bo` is not
backend-tagged, so one `.bo` must serve both backends and may contain no
backend-dependent definition. On the Bluesim side, `simExpand`
(`src/comp/SimExpand.hs`) builds one `SimPackage` per *module type* from
each `ABinModInfo` the hierarchy walk found; `simMakeCBlocks` makes one C++
class per module (`MOD_<name>`); the user-module naming function ignores
instantiation arguments, so two instances of one module with different
`parameter` values share a class and receive the values as constructor
arguments (`PARAM_` members, `mkStateInitList` in `src/comp/SimCCBlock.hs`);
instantiation arguments must be constants (`EBSimDynamicArg`); `SimExpand`
canonicalizes an `Integer` parameter to `ATBit 32`; per-module C++ object
reuse and the fork's `-c` byte-identity mode key on the module name
(`src/comp/SimFileUtils.hs`, `DEVELOP.md`). The `.ba` stores the APackage
before `aState` (so before the Verilog-only inlining passes), after
`Params.iParams` and `aDropUndet`. Libraries are
built with no backend flag (`src/Libraries/common.mk` passes `-bdir
$(BUILDDIR)` and `-vsearch $(BUILDDIR)`; `src/Libraries/Base1/Makefile`
says "Only .bo files are generated"); the Verilog search path is `vdir`
(or `.`), then the `-p` entries, then `$BLUESPECDIR/Libraries`, then
`$BLUESPECDIR/Verilog` (`FlagsDecode.hs`
`def_vpath`), and the library install copies `$(BUILDDIR)/*` into
`inst/lib/Libraries`. `Depend.getPkgInfo` puts every `PPverilog` def into
`gens` and `getGenFs` expects a `.v` (Verilog) or `.ba` (Bluesim) for each.
The testsuite compares Verilog with `compare_verilog` (header stripped,
`__h`/`__d` renumbered), supports Verilator (`-use-dpi` implied) and runs
both backends in `test_c_veri_bsv_modules`; `testsuite/bsc.verilog/
parameters/` covers value parameters but no generated size parameter.
Library zero-width branches: `mkReg`/`mkRegU`/`mkRegA` (`if valueOf sa == 0
then stub else vMkReg`), `mkRWire` (`RWire0`), `wrapRegFile`, every
`FIFOF_.bsv` wrapper (`FIFO10`/`FIFO20`/`SizedFIFO0`), all decided at the
parent's concrete instantiation.

## DESIGN (decided; deviate only with a reason stated in your spec)

### 3.1 Scope: width-generic modules

A def is **parameterized-synthesizable** iff it carries `PPverilog` and the
new `PPparameterized` (Classic `{-# verilog m { parameterized } #-}`, BSV
`(* synthesize, parameterized *)`), has an explicit type signature, and its
type variables are all of kind `KNum`. The parameter names are the type
variable names in signature order (the `Fork.bs` convention), so `mkFIFO2
:: Module (VFIFO2 width)` yields `parameter width`. Non-numeric type
variables or non-numeric provisos (anything but the numeric classes the
typechecker's solver knows: `Add`, `Mul`, `Div`, `Max`, `Min`, `Log`,
`NumEq`), including `KStr` variables, raise T0041 (`ENotKNum`, revived;
the parameterized path runs its own kind check *before* `chkType`'s
proviso and type-variable gates, which would otherwise report T0043
first) with a message naming the
variable or proviso. A missing signature is an error. `Bits a sa`-style
payload polymorphism is deliberately excluded: the core takes `Bit width`
payloads and the library wrapper does `pack`/`unpack`, which is how the
Verilog library is already structured.

Size parameters may be used in **types** (`Bit width`, `Bit (TAdd width
1)`, `Bit (TLog depth)`) and in **values** (`valueOf width` as a symbolic
`Integer` that flows into bit values, arithmetic, and submodule Verilog
parameters). They may not decide **structure**: a `Vector width`, a loop
bounded by `valueOf width`, a module or rule whose existence depends on a
condition over size parameters, a dynamic array index of symbolic width,
`primUninitBitArray`/`primUpdateBitArray` at symbolic width. Conditions on
size parameters are allowed exactly when they are decidable from the
assumptions in 3.5; otherwise a user error names the condition and the
position.

Every size parameter is assumed `>= 1`. The Verilog library has the same
convention (`parameter width = 1`, "only for n>0"), bsc elides zero-width
ports, and the library wrappers route width 0 to separate zero-width
modules at the parent's concrete instantiation (3.9). The generated wrapper
checks the assumption at each instantiation (3.6).

### 3.2 Symbolic sizes in ASyntax

Change `ASize` to a sum type, not a parallel constructor:

```
data SizeExpr = SELit Integer | SEVar AId
              | SEAdd SizeExpr SizeExpr | SESub ... | SEMul ... | SEDiv ...  -- TDiv is ceiling (TypeOps.divC)
              | SEExp SizeExpr | SELog SizeExpr | SEMax ... | SEMin ...     -- mirror TypeOps.opNumT
type ASize = SizeExpr
instance Num SizeExpr   -- (+), (-), (*) build nodes, folding when both literal; fromInteger = SELit;
                        -- abs/signum are internalError
instance Eq SizeExpr    -- structural after a normalizer that folds literals and sorts commutative operands
isConcreteSize :: SizeExpr -> Maybe Integer
sizeToVExpr :: SizeExpr -> VExpr   -- VEConst, VEVar, VEOp with VAdd/VSub/VMul/VQuot, ceiling div as (a+b-1)/b,
                                   -- SEExp as (1 << x), SELog as VEFctCall "$clog2", SEMax/SEMin as VEIf
```

Instances: `Eq` (structural over the normalized form), `Ord` (a total
order over the normalized structure, needed because `AType`, `AExpr`,
`ADef`, `AAction`, `AClock`, `AReset` and `AInout` derive `Ord` and are
used as container keys; it is *not* a numeric order), `Show`, `NFData`
(`rnf (ATBit sz) = rnf sz` in ASyntax), `Bin`, `PPrint`, and `Num` as
above. No `Integral`, `Enum` or `Real` instance. Change `ATypeC.aSize` to
return `SizeExpr` (the `ATTuple`/`ATArray`/`ATString`/`ATReal` cases build
`SELit`/`SEMul`); that, not `atb_size` alone, is what pushes the type
errors into the `aSize`-heavy files. Reason for the shape: every existing
`ATBit n`, `ATBit 1`, `ATBit 0` pattern keeps compiling (literal patterns
desugar to `== fromInteger k` and a symbolic size simply fails them, which
is the conservative behavior at the 1-bit simplifications in AOpt, at
`fixupZeroBit`, at `vSize (ATBit 1)`), `sum (map aSize es)` and `n - 1`
keep type-checking and now build symbolic arithmetic, and every site that
folds a *value* from a size (`2^n`, `[0..n-1]`, `genericLength`, `div`,
`itos`, `VEConst n`, bit-vector sort creation) becomes a GHC type error,
so the compiler enumerates most of the sites to audit instead of a new
constructor silently falling into wildcards such as `isNotZeroSized _ =
True`. Because `Ord` must exist, comparisons are *not* caught by the type
checker: `<`, `<=`, `>`, `>=`, `compare`, `max`, `min`, `maximum`, `sort`
on sizes must be found by grep over `aSize`, `atb_size` and `ATBit`
patterns, starting with `cheap PrimEQ` in `src/comp/AExpand.hs` (`sz <=
24`) and the sign/zero-extend check in `src/comp/ACheck.hs` (`n <= m`), and
guarded with `isConcreteSize`. Only `atb_size` becomes symbolic in this task; `ATArray`,
`ATString`, `ATAbstract` sizes stay `Integer` (structural; a symbolic one
is an error at AConv). Add `Bin SizeExpr` for `.ba` round-trips and a
`PPrint` instance.

Audit rule for every site the type checker flags: fold or transform only
under `isConcreteSize`; otherwise leave the expression alone (AOpt,
AVeriQuirks constant folding, ADropUndet's `mkUnspec`, AExpand cost
heuristics treat symbolic as "not cheap"), or raise a clear error where the
construct is structural (Synthesize's bit-blasting, AUses' array-index
domain, ForeignFunctions' DPI width-mangled names: use the non-DPI task
path or error).

### 3.3 Front end: pragma, GenWrap, inner def, wrapper

1. `src/comp/Pragma.hs`: `PPparameterized`; Classic spelling in
   `pVeriGenProps` (`src/comp/Parser/Classic/CParser.hs`), BSV attribute in
   `attributes2modpprops`/`attribute2modpprop` (`src/comp/Parser/BSV/
   CVParser.lhs`); `Bin PProp` tag in `src/comp/BinData.hs` (use 36;
   `PPdefault_reset_arg` is 35 at the base commit and 3, 10, 11 are
   retired gaps, do not reuse them); bump the `.bo` and `.ba` headers
   (`GenBin.hs`, `GenABin.hs`). Also add `PPverilogName String` (Classic
   `verilog_name = "..."`, BSV `verilog_name`), which does not exist yet
   in this tree, with its own tag.
2. `Depend.getPkgInfo`/`getGenFs`: a `PPparameterized` def is an ordinary
   `gen` (a `.v` under Verilog, a `.ba` under Bluesim, both under `-elab`),
   so no change is needed there. bluetcl `defs module` lists it as a
   synthesized module.
3. `GenWrap.getDef`/`chkType`: for a parameterized def, accept `KNum` type
   variables and numeric provisos; reject everything else with T0041; keep
   the interface-shape gates (polymorphic fields, non-interface,
   non-module, interface or function arguments). Build the `IfcTRec`
   through the foreign-record machinery rather than `makeIfcTRec`:
   `rec_numargs` = the `KNum` variables in signature order, `rec_kind =
   foldr (\_ k -> Kfun KNum k) KStar rec_numargs`, `rec_typemap` from a
   `procType`-style fold restricted to those variables (fields already of
   type `Bit width` map to themselves; a field of a non-`Bit` type over a
   size variable, such as `Vector width Bool` or a struct containing `Bit
   width`, is flattened through `WrapField` as today, with the proviso
   carried on the record). `genTDef`/`genIfc` then declare `interface
   VFIFO2_ width`.
4. `mkTo_`, `mkFrom_`: add equations for non-empty `rec_numargs` and
   `rec_typemap` (the flattened type is `cTApplys (cTCon tyId) (map TVar
   rec_numargs)`; the conversion defs are polymorphic in those variables);
   `mkGeneric` must apply the numeric arguments to `flat_id` instead of
   using `cTCon flat_id` bare.
5. `mkNewModDef`: the inner def is `mkFIFO2<suffix> :: Module (VFIFO2_
   width)` keeping the def's `forall` and numeric provisos, so after
   typecheck and `iConvVS` it is `ILAM width IKNum (ILam dAdd ... body)`.
   The typechecker inserts a dictionary lambda per proviso into the
   clauses (`dict_vs` in `TCheck.hs`) and `iConvCs` turns them into leading
   `ILam d <dictType>` binders under the `ILAM`s (`foreignPredCount` in
   IConv is a different mechanism: it drops dictionary *arguments* at
   application sites of `Cforeign` vars, so it does not apply here). The
   numeric classes have no methods and the body never references these
   binders, so `extractModuleArgs` strips them (3.4.1). The provisos
   themselves are kept as `[Pred]` (over `CType`) on the `WrapInfo` (new
   field `wi_size_preds`) for the evaluator (3.5).
6. `mkDef` (the wrapper): keep the def's original `CQType`; the body is
   `liftModule (xWrapperModuleVerilog ... name wire_info args ...)` exactly
   as for a monomorphic module, with no backend selection of any kind: the
   same wrapper is an import of `FIFO2.v` under Verilog and of `FIFO2.ba`
   under Bluesim (3.8). The `wire_info` comes from elaboration and must
   carry one `Param (VName "width")` per size parameter at its head (3.4);
   `mkDef` prepends the matching argument expressions, built the way the
   parsers build `valueOf`: `cVApply idValueOf [CHasType (anyExprAt pos)
   (CQType [] (TAp (cTCon idBit) (TVar width)))]` (`TCheck.hs` special-cases
   exactly that shape). `xWrapperModuleVerilog` and `xCmoduleVerilog` live in
   `src/comp/CSyntax.hs`; `xWrapperModuleVerilog` appends the default
   clock/reset arguments *after* `args` and `xCmoduleVerilog` zips the wire
   info's `VArgInfo` list with the argument expressions positionally
   (internal error on a length mismatch), so the `Param` entries and their
   expressions must both be prepended, ahead of the module's own
   clock/reset/port/parameter arguments. Keep `is_user_import = False` (the
   `False` that `xWrapperModuleVerilog` already hard-codes) so the `.ba`
   hierarchy walk follows the instance by name and finds `<name>.ba` on
   the path, as for any synthesized submodule. The module name is the
   def's base name; honor the new `verilog_name = "FIFO2"` pragma
   (`PPverilogName`, 3.3.1) for the module name literal, `apkg_name` and
   the `.v`/`.ba` file names, with the same change set the sibling prompt
   lists (GenWrap `mkDef`, `AConv.apkg_name`, `modstr` in `genModule`/
   `writeABin`, `Depend.getGenFs`, bluetcl `defs module`).
7. `-g mkFoo` on a parameterized def is allowed (it generates the
   parameterized `.v`); `-g` on an ordinary polymorphic def keeps today's
   error.

### 3.4 Elaboration with symbolic sizes

1. `extractModuleArgs`: strip leading `ILAM i IKNum e` binders, recording
   `(i, IKNum)`, then strip the leading `ILam` binders whose type is a
   numeric-class dictionary (`ITCon` of `idAdd`/`idMul`/`idDiv`/`idLog`/
   `idMax`/`idMin`/`idNumEq` applied); an `ILAM` of kind `IKStar` or
   `IKStr` → T0041, keeping the existing `EBadIfcType` report when
   `getNonSynthTypes` identifies a non-bitifiable *argument*. Thread the
   list back so `iExpandModuleDef` returns real `iks`. Do **not** add
   entries to `imod_external_wires`: `getAPackageInputs` zips
   `apkg_external_wires` with `apkg_inputs` and internal-errors on a length
   mismatch, and AState/APaths consume that zip; the size parameters
   already travel as `apkg_size_params` (AState's `size_ps`). The wrapper's
   `VWireInfo` is built separately at the `deffun` call in `bsc.hs`
   (`wireinfo = apkg_external_wires amod_final`) by prepending one `Param
   (VName (getIdBaseString i))` per `apkg_size_params` entry.
   Keep each binder as a free `ITVar i` during evaluation; register the set
   of size parameters in `GStateRO` (`g_size_params :: [Id]`) together with
   the provisos (3.5).
2. `PrimValueOf` on `ITVar i` with `i` a size parameter: return `ICon i
   (ICModParam itInteger)`; keep the `Id` as the type variable's `Id` (that
   is the link AConv needs). Not a size parameter: today's internal error
   becomes a user error.
3. Integer primitives (`integerPrim`): when an operand is a size parameter
   or an expression over them, build a residual application for `+`, `-`,
   `*`, `div`, `mod`, `max`, `min`, `log2`, `exp2`; for comparisons and
   equality, consult the oracle (3.5); anything else (`primIntegerToString`,
   bit-ops on Integer, `$display` of an Integer that is symbolic) is a user
   error "size parameter `width` used in a non-synthesizable Integer
   operation". `evalInteger` callers that need a literal (loop bounds,
   `primArrayNew`, `Vector` lengths, `replicateM`, `mkSizedFIFO` depth as an
   Integer argument of a non-parameterized module) raise the structural-use
   error at the caller's position, never an internal error.
4. `PrimIntegerToBit`/`UIntBits`/`IntBits` with a symbolic target width or
   a symbolic Integer (new `conAp'` clauses for `[T (ITVar k), E e]`; today
   that shape reaches the catch-all internal error): produce `ICon i
   (ICModParam (Bit k))` for a plain `valueOf` (the fork's `handleInt`
   shape) and a residual application otherwise; no range check (as the
   fork already documents for symbolic
   values). A literal of symbolic width (`0 :: Bit width`, `fromInteger 5`)
   is an `ICInt` whose `iConType` is `Bit (ITVar width)` (the shape
   `PrimZeroExt` already builds); `ilWidth` stays `Nothing`.
5. Bit primitives with symbolic type arguments: make the non-folding
   explicit. `isIntLit` stays as is, but `doPrimOp` must return `Nothing`
   when any type argument is not `ITNum` (replace the silent `tints`
   filter), including when called from `ITransform.iTrAp`. The strict
   primitives then build residual applications typed through `iGetTypeNorm`
   (whose fast paths need `ITNum` and whose fallback `tCheck`/`tSubst` path
   must be verified to produce `Bit (TAdd ...)` types for `PrimConcat` and
   `Bit (ITVar)` for the rest). `PrimPack`/`PrimUnpack` hold-mode
   (`ICLazyPack`) already handles symbolic payloads; the identity fast path
   `ta == aitBit tn` must compare normalized types (3.4.8).
6. `iToCT`: map `ITVar i` to `TVar` so `PrimTypeOf`, `PrimPrintType`,
   `primSavePortType` and `doBuildUndefined` work at symbolic types; an
   undetermined value at `Bit width` is `ICUndet` at that type and lowers
   to `ASAny` with a symbolic width.
7. `chkStateVarTypes`: allow free type variables that are size parameters.
   Submodule instantiation arguments that are size-parameter expressions
   (`("width", valueOf width)` inside the core's `mkRegU`) pass
   `chkModuleArgument` (empty wire set) and `Params.isConstIExpr`
   (`ICModParam` accepted) unchanged.
8. Normalize symbolic numeric types: `TAdd 1 width` and `TAdd width 1`
   must compare equal where the evaluator compares types (`pack`/`unpack`
   cancellation, `improveIf`, `chkStateVarTypes`); add a canonicalizer in
   `IType.hs` (fold literals, sort commutative operands) and use it in
   `mkITAp` so interned symbolic types are canonical.
9. Hard errors for structural uses: `PrimArrayDynSelect`/`Update` with a
   symbolic index size, `PrimUninitBitArray`, `PrimUpdateBitArray` at
   symbolic width, `bitTupleSizes` on a symbolic `Bit` (today silently 0),
   `-split-if` on a symbolic condition, `noinline` functions or `BDPI`
   foreign calls with symbolic-width operands.

### 3.5 Deciding conditions on size parameters

Capture the def's numeric provisos as `[Pred]` over `CType` in GenWrap
(`wi_size_preds`) and thread them through `genModule` → `iExpand` → `runG`
into `GStateRO`, together with the implicit `width >= 1` for every size
parameter (represent it as `Add 1 k width` with a fresh variable `k`). When an
Integer comparison or equality has a symbolic operand, or `doIf`/`PrimCase`
sees a condition built from such comparisons, translate the condition to a
`Pred` (`NumEq`, or an inequality encoded as `Add`) and ask the solver.
Add a three-valued entry point to `SATPred`/`Pred2Yices`/`Pred2STP`
(`decidePred :: SATPredState -> [Pred] -> Pred -> IO (Decision,
SATPredState)` with `Proved | Refuted | Unknown`; the current `solvePred`
conflates refuted and unknown). `Proved` folds to `True`, `Refuted` to
`False`, `Unknown` is the user error "cannot decide `valueOf width == 3`
from the provisos of `mkFoo`; add a proviso or restructure". Create one
solver session per atomic IO block as `TCMisc.batchSolveNumericPreds` does
(the Yices binding resets on a second context). This is what lets
`mkRegU`'s `if valueOf sa == 0` (and every other library zero-width branch)
elaborate inside a parameterized core: `sa == 0` is `Refuted` under `sa >=
1`.

### 3.6 Parent side

Nothing new is needed for the instantiation: the wrapper is a
`CmoduleVerilog` whose parameter expression `valueOf width` folds to an
`Integer` literal at the parent's concrete type, so `paramExprs` emits
`#(.width(32'd32))` exactly as for today's BVI imports, and the instance's
port widths come from the wrapper's method types at the parent's type.
Add, in the wrapper, a check that each size argument is `>= 1` (a static
assertion evaluated at the parent: `if valueOf width == 0 then error
"parameterized module mkFoo instantiated at width 0"`), so the library
wrappers' zero-width branches remain the only way to reach width 0.

### 3.7 Back end

AConv: an `IType -> SizeExpr` converter for `Bit` types over size
parameters and type functions (`TAdd`→`SEAdd`, ..., `TLog`→`SELog`);
`primType` for `PrimConcat`/`PrimMul`/`PrimQuot`/`PrimRem` builds symbolic
sums; `eTrunc` compares only when concrete. `ICModParam` at `Integer`
type already lowers through `aTypeConvE`'s fallback to an `ATAbstract
idInteger []`-typed `ASParam`, and AVerilog already prints a non-`ATBit`
parameter without a range; what changes is AState's `param_inputs`, which
types the size parameters `aTNat` (`ATBit 32`) and would print `parameter
[31:0] width = 32'd0;`: type them `ATAbstract idInteger []` with default
`1`, so the module declares `parameter width = 1;`. `ICModParam (Bit k)` lowers to `ASParam
(ATBit k)`; residual Integer arithmetic lowers to `APrim` over `ATBit 32`
with `ASParam` leaves, and `PrimIntegerToBit` of such an expression to a
zero-extension or truncation to the target width.

AState: declare size params first in `aspkg_parameters` with the
`Integer`-typed default of 1; keep `aSize ty == 0` tests (never true for a
symbolic size). APaths: remove the "size parameters not supported"
internal error; size params need no path handling.

AVerilog/AVerilogUtil: `vSize (ATBit n)` → `Just (sizeToVExpr (n - 1),
VEConst 0)` for symbolic `n` (never `Nothing`); module port and instance
output declarations likewise; `VAParameter` for size params with no range
and default `VEConst 1`; `vco_def_widths :: M.Map AId Integer` becomes
`M.Map AId SizeExpr` (or `Maybe Integer`); the
`-1:0` guard (`nonZero`) must not evaluate a symbolic size. Constants: add
`VEWConstSym VExpr Integer Integer` (width expression, base, value) and
`VEUnknownSym VExpr String`, printed as `{W{1'b0}}` for zero, `{W{1'b1}}`
for all-ones, `{W{1'bx}}`/`{W{1'bz}}` for unknowns, and for any other value
`v` of minimal bit-length `k`, a hoisted `wire [W-1:0] c = k'hV;`
(assignment context zero-extends; `AVeriQuirks` has the `mkDefS`-style
naming to hoist into) with a user error when `W >= k` is not provable from
the assumptions. `PrimZeroExt` prints `{ {(W-k){1'b0}}, x }` (requires `W
> k` provable, else hoist), `PrimSignExt` uses `VERepeat` of a symbolic
count, signed compares use `$signed`. `muxInst` and the Classic-foreign
numeric parameters pass `sizeToVExpr`. The `Mux_n` primitives are selected
by arity, so no change.

InlineReg: `mkRegInstInfo` accepts any constant width expression
(`ASInt` or an `ASParam`-based expression) and declares `reg [W-1:0]`; the
initial block prints `{((W+1)/2){2'b10}}` (the `FIFO2.v` form, legal in
assignment context). InlineWires and InlineCReg take the width from
`avi_iargs` through the same helper. VIOProps prints the size expression.
AVeriQuirks: guard the dynamic `PrimExtract` rewrite, `PrimSRA` masks and
`aBitOr`/`aBitAnd` folding with `isConcreteSize`; when symbolic, keep the
primitive and print `e[l +: W]` (Verilog-2005 indexed part-select) and
`$signed(e) >>> k`; `fixupZeroBit` is never hit. AOpt: wrap every listed
site (`2^sz` dyn-select expansion, bit-constant optimization, `complete`,
mux-of-concat splitting, `joinPairs`, `aSelect`/`aExtract`, `aZeroExt`)
with `isConcreteSize`. AExpand: symbolic is "not cheap". ADropUndet: leave
`ASAny` in place when symbolic. ACheck: equalities are structural on
normalized `SizeExpr`; `n <= m` and `2^sz > i` checks apply only when
concrete.

Verilog dialect: `$clog2`, zero replication inside a concatenation and
`+:` part-selects are Verilog-2005 features. Require `-verilog-2005`-level
output for parameterized modules that use `TLog`, dynamic extracts or
zero-length padding (bsc has a `systemVerilogOutput` flag; add a
Verilog-2005 flag if none exists) and error otherwise; `FIFO2`-class cores
need none of these.

Scheduling: in `AExpr2STP.convAExpr2SExpr` and `AExpr2Yices.convAExpr2YExpr`,
when an expression's type is a symbolic `ATBit`, do not create a sort; at
the enclosing comparison, equality or extract primitive call `addUnknownExpr
mty (whole primitive) 1` so the result is a fresh 1-bit unknown. Boolean
structure over such unknowns is still modelled (`!full && !empty` keeps its
mutual-exclusion reasoning); nothing is ever proved through payload bits.
`getBitType` and the `PrimSignExt` width path must not be reached for
symbolic types.

`.ba`, formal, bluetcl: `writeABin` writes the parameterized module's `.ba`
under `-sim` and `-elab` as for any module, with symbolic sizes (`Bin
SizeExpr`, the new `AExpr`/`VExpr` forms); `apkg_size_params` is already
serialized. `convAPackageToLambdaCalc`/`SAL` and `-synthesize` raise a user
error for parameterized modules. bluetcl `module load` of the parameterized
module shows sizes as expressions (`PPrint SizeExpr`); `-show-schedule` and
`-show-rule-rel` work since they run in `genModule`.

### 3.8 Bluesim: link-time instantiation of a parameterized `.ba`

Bluesim code generation stays width-concrete. The new step,
`instantiateTemplates`, lives in `simExpand` (`src/comp/SimExpand.hs`)
between `getABIHierarchy` and `simpkgs <- mapM simExpandABin`, where the
link holds `modinfos_used_by_name :: [(String, (ABinModInfo, String))]`,
the `HierMap` (keyed by module name string only; `followABMIHierarchy`
skips a module already in the map, so today two instances with different
arguments share one entry), the `InstModMap` (hierarchical instance path to
module name, built by `hierMapToInstModMap`, consumed by `findInstMod`,
`moveDefsOntoStack`, `doTickCall` and the schedule statement generation)
and the `ABinMap` file map (module name to `.ba` path; `SimFileUtils.isStale`
internal-errors "unknown package" for a module absent from it). Everything
downstream keys on `sp_name`/`getModuleName`: `name_map` in
`simMakeCBlocks`, the C++ class `MOD_<sb_name>`, the `<name>.cxx`/`.h`/
`_backing` files, the VCD/FST scope's module type. The step:

1. Walk the loaded packages top-down from the root (the Bluesim top has
   no parameters, `EBSimTopLevelArgOrParam`, so a parent's own `ASParam`s
   are literals by the time its children are visited). For every `AVInst`
   whose module's `ABinModInfo` has a non-empty `apkg_size_params`, recover
   the binding with `getInstArgs`/`getParams`/`getVArgInfoName` and evaluate
   each value with `APrims.evalAExprToInteger` (after `simExpandParams` an
   argument is constant but not necessarily an `ASInt`: `isConstAExpr`
   admits `APrim` over constants and `ASParam`); a non-constant is
   `EBSimDynamicArg`, which `checkInstArgs` already raises.
2. Key = (module name, [(parameter, value)] in `apkg_size_params` order);
   name = module name followed by `__<param><value>` per parameter
   (`FIFO2__width32`, `SizedFIFO__width8__depth16`; the pattern of
   `ForeignFunctions.mkDPIMonoName`). There is no sanitizer on `sp_name`
   (the C++ class and file names use it verbatim), so restrict to
   `[A-Za-z0-9_]`, and the name must not collide with a `primBlocks`
   `sb_name`. Instantiate once per distinct key.
3. Instantiation of the `ABinModInfo` copy: (a) a new type pass, because
   no `AType` traversal exists (`mapAExprs` never rewrites `ae_type`,
   `aSubst` never touches types): substitute `SEVar width` by `SELit 32`
   in `apkg_inputs` (`AAI_Port`), `apkg_external_wire_types` and
   `avi_port_types` (these are `IType`: `ITNum`), `avi_type`,
   `avi_meth_types`, `avi_vmi`, every `adef_type`, `aif_inputs`,
   `ataskact_value_type`, and the types inside expressions; set
   `apkg_size_params = []` and drop the size parameters from the parameter
   inputs. (b) `aSubst` with `width ↦ ASInt (ATBit 32) 32` over the
   package (`aSubst` already substitutes `ASParam` leaves by id and
   `SimPackage`/`APackage` have `AExprs` instances); size-parameter leaves
   carry `ATBit 32` in the `.ba` (AState's and `SimExpand`'s canonical form
   for `Integer` parameters), so residual Integer arithmetic folds in
   32-bit arithmetic, which is adequate for sizes. (c) A bottom-up fold of
   every `APrim` whose arguments are now literals, using
   `evalAExprToInteger` (`Prim.evalPrimToInt`); `AOpt.aPrim` does not fold
   `PrimAdd`/`PrimSub`/`PrimMul`, so this fold is new, and it is mandatory
   rather than an optimization because the primitive naming functions
   (`sizedType`, `regType`, `memType` in `SimPrimitiveModules.hs`)
   pattern-match an `ASInt` size argument and internal-error otherwise.
   Write the substitution and fold as plain bottom-up recursion, not as an
   `exprMap` callback (`exprMap` applies the callback to the unprocessed
   node and skips the children when it returns `Just`). (d) `aDropUndet
   errh abmi_flags` (the `.ba` may carry `ASAny t Nothing` of now-concrete
   width; `SimPackageOpt.convertASAny` would also handle it, but the
   recommended-value form needs concrete sizes). (e) `simCheckPackage errh
   True` on the copy; (f) `ACheck.aMCheck` as an assertion. Value
   parameters (`guarded`, `init`) stay parameters and keep flowing as
   constructor arguments (`PARAM_` members) as today.
4. Rewrite the parent's `AVInst`: `vName (avi_vmi)` to the mangled name
   (the hierarchy and `mkState` resolve instance to module through it),
   remove the size-parameter entries from `vArgs` and `avi_iargs`. Append
   the copy to `modinfos_used_by_name` under the mangled name, add it to
   the `HierMap` with its own children and re-point the parent's `(inst,
   mod)` pair, recompute the `InstModMap`, and register the copy in the
   file map pointing at the template's `.ba` (its timestamp source) so
   object reuse works; alternatively skip reuse analysis for derived
   modules. Nested parameterized modules (`SizedFIFO` instantiating a
   memory with `.addr_width($clog2(depth))`) are instantiated by the same
   walk after substitution turns their arguments into literals; detect and
   reject cycles.
5. Reuse the stored schedule and path information unchanged: Bluesim
   reads only `asi_sched_graph`, `asi_schedule`, `asi_exclusive_rules_db`
   and `asi_rule_relation_db`, relations over rule and method ids with no
   widths in them, and the module was scheduled with every
   payload-dependent condition treated as unknown (3.7), so the stored
   schedule is valid, if possibly conservative, at every width; a concrete
   width could only remove conflicts, never add one. Do not re-schedule.
   The use maps and `abmi_method_dump` may stay symbolic in the copy;
   Bluesim does not read them.
6. The `-c` byte-identity harness (`check_block_codegen_modules`) and
   per-module object reuse key on module names. A derived module's C++
   must be byte-identical across links for the same key: deterministic
   name, deterministic traversal, and the existing name-sorting discipline
   for ids (`DEVELOP.md`, `-c` section). `-c` today emits only the root's
   files; make `-c <parent>` also emit its instantiated children, or let
   `-c` take a parameter binding for a template. Decide and document which.
7. Visibility: the FST writer records the mangled name as the scope's
   module type (`fstWriterSetScope`), VCD ignores it; Bluetcl `sim ls`
   shows kinds only; `bluetcl module submodules` re-walks the `.ba`s and
   reports the template name `FIFO2`. Accept the mismatch and document it,
   or strip the `__...` suffix in the FST module type.

This is the mechanism that replaces a Bluesim primitive: once a reference
core ships `FIFO2.ba` and `FIFO2.v` with the same import name and
parameters as the hand-written primitive, deleting the `FIFO2` row from
`primMap` (and the name-keyed helpers that assume it) makes the hierarchy
walk resolve `FIFO2` to the `.ba` instead of the C++ model. Emitting
width-generic C++ (`template <int width> class MOD_FIFO2`) is a possible
later refinement of step 3 only; it needs the same `.ba`, so nothing in this
prompt changes if it is done.

### 3.9 Library build and installation

Packages that define parameterized modules must be compiled with `-verilog
-vdir $(BUILDDIR)` so the generated `.v` lands in `inst/lib/Libraries`,
which is already on the default `-y` path, and `Base1/Makefile`'s clean
target must remove `*.v` there. The hand-written `src/Verilog/*.v` stay
until each family's generated file has passed the lockstep tests; the
generated file must not share a name with a hand-written one still
installed in `inst/lib/Verilog` (search-path order would pick the generated
one first; make the clash a build error in `src/Verilog/common.mk`).

### 3.10 Library structure under this design

The two-layer structure stays: `FIFOF_.bsv`'s `vMk2FIFOF`-style import is
replaced by the parameterized core `mkFIFO2 :: (Add 1 k width) => Module
(VFIFO2 width)` (Classic has no `_` type wildcard; use a named variable)
written in Classic with the port-naming attributes
(`prefix = ""`, `arg_names = [D_IN]`, `enable = "ENQ"`, `result =
"D_OUT"`, `always_ready`, `reset_prefix = "RST"`, `parameter guarded`),
and the outer wrapper keeps its `valueOf sa == 0` branch to the zero-width
variant and its `pack`/`unpack`. Under `-sim` the core is instantiated at
link from its `.ba` (3.8). The schedule and port-type fidelity items in
`doc/design/size_polymorphic_synthesis.md` section 4 apply unchanged and are
not part of this task.

## CONSTRAINTS

- Monomorphic `synthesize` modules produce byte-identical `.v` and `.ba`
  before and after (the `ASize` change is M0 and must land with zero
  golden changes).
- No change to `src/bluesim/`; Bluesim code generation (`SimMakeCBlocks`,
  `SimCCBlock`, `SimBlocksToC`) stays width-concrete and unchanged; the
  only Bluesim-side addition is the instantiation step in `SimExpand` (3.8)
  and the derived-module handling in `SimFileUtils`/`-c` mode.
- No implementation selection by `genC`/`genVerilog` (or any other
  backend-dependent definition) in compiler-generated code or in the `.bo`.
- Any `.bo`/`.ba` format change bumps both header tags.
- `-Wall` is on; `SizeExpr` has no `Integral`/`Enum`/`Real`, so sites
  that fold sizes fail to compile until audited; do not add those
  instances to make errors go away. `Ord` must exist (container keys), so
  the comparison sites are audited by grep (3.2); record the grep and its
  result in the spec.
- New logic in new modules where possible (`src/comp/SizeExpr.hs` for the
  type, normalizer and printer; `src/comp/SizeDecide.hs` for the oracle);
  hooks in existing modules as small as the design allows.
- Every unsupported construct is a user error at a source position with the
  size parameter named; never an internal error and never silently wrong
  Verilog (a symbolic width treated as 0 or 32 is the failure mode to
  guard against: grep for `aTNat`, `bitTupleSizes`, `ATAbstract idBit`).
- Do not open pull requests; push only to the branch you were given.

## APPROACH

1. Explore; confirm every function name above against the tree you are on.
2. Write `doc/design/parameterized_verilog_spec.md`: the `SizeExpr` type and
   normalizer; the exact `AType`/`AExpr`/`VExpr` additions; the GenWrap
   record path for parameterized defs with one worked example (a FIFO2-like
   core with `parameter guarded` and a `TAdd` field type); the
   `extractModuleArgs`/`iks`/wire-info changes; the oracle API and how
   provisos reach `GStateRO`; the list of evaluator primitives with their
   new symbolic behavior (fold / residual / error); the back-end audit
   list; error messages; tests. Commit it and return it for review
   **before** writing compiler code.
3. After approval, build in this order, each step green before the next:
   - **M0** `ASize = SizeExpr` with the `Num` trick; fix every compile error
     conservatively; full testsuite byte-identical. (Largest mechanical
     step; independently valuable; expect 1000 to 2000 lines of mostly
     mechanical diff.)
   - **M1** vertical slice: pragma, GenWrap record path, inner def with
     `ILAM`, wrapper with `Param` entries, `imod_type_args`,
     AState/AVerilog `parameter width = 1;`, APaths unblock, `PrimValueOf`
     to `ICModParam`, the `>= 1` assumption deciding `== 0`/`/= 0` only,
     `vSize`/port/reg printing of symbolic ranges, `.ba` with symbolic
     sizes, and the Bluesim link-time instantiation of 3.8 for a module
     with one size parameter and no residual arithmetic. Target: `mkPass`
     above generates `mkPass.v`, and a parent instantiating it at five
     widths co-simulates under Verilator and Bluesim with identical output.
   - **M2** evaluator and back end for the FIFO class: residual bit
     primitives, symbolic literals and unknowns, `iToCT`, `chkStateVarTypes`,
     InlineReg/Wires/CReg, AOpt/AVeriQuirks/AExpand/ADropUndet guards, SAT
     intercept, structural-use errors. Target: reference FIFO1, FIFO2,
     FIFOL1, FIFOL2, Counter cores generate Verilog matching the
     hand-written files' ports, parameters and register names and pass
     Verilator lockstep at the widths listed in WHAT.
   - **M3** provisos and the three-valued oracle, residual Integer
     arithmetic, `TLog`/`$clog2`/`+:` with the dialect gate (target:
     SizedFIFO with `width` and `depth` parameters), the full Bluesim
     instantiation (nested parameterized modules, residual arithmetic
     folding, `-c` byte-identity for derived modules), `verilog_name`,
     library build plumbing (3.9), `-elab`/formal/bluetcl behavior, user
     guide text (`doc/user_guide/user_guide.tex`, the `synthesize`
     attribute section, and the reference guides' statement that bsc does
     not create parameterized Verilog).
   - **M4** the first replacement: the reference FIFO2 core with
     `verilog_name = "FIFO2"` ships `FIFO2.ba` and `FIFO2.v`, the `FIFO2`
     row leaves `primMap` and the name-keyed helpers, and the FIFO tests in
     `testsuite/bsc.lib/fifo` run against the reference under both
     backends. (The remaining families follow the plan in
     `doc/design/size_polymorphic_synthesis.md` sections 5 to 7 and are not
     part of this task.)
4. Tests, in a new `testsuite/bsc.verilog/sizeparams/` (a sibling of
   `parameters/` and `noinline/`; `Makefile` copied from
   `testsuite/bsc.verilog/noinline/Makefile`), with `sizeparams.exp` using
   the suite's existing procedures (`compile_verilog_pass`,
   `compare_verilog`, `find_regexp`, `find_n_regexp`,
   `test_c_veri_bsv_modules`, `compile_verilog_fail_error`): `mkPass`
   header and golden; a parent instantiating it at 1, 8, 32, 64, 128 with
   five `#(.width(32'd...))` matches, co-simulated under Verilator and
   Bluesim, with the Bluesim build checked for the five derived classes
   (`mkPass__width1` ... `mkPass__width128`), a VCD scope per instance, and
   `-c` byte-identity across two links; two instances at the same width
   sharing one derived module; a core with `parameter guarded` and a `TAdd
   width 1` field; a
   `TLog depth` core under the dialect flag and its rejection without it; a
   submodule instantiated with `.width(width)` passed down; `ICLazyPack` at
   symbolic width through a struct wrapper; rejection tests for `Vector
   width`, a loop to `valueOf width`, an undecidable `if`, a non-numeric
   type variable (T0041), a missing signature, a `BDPI` call at symbolic
   width, `-synthesize`, instantiation at width 0; the lockstep tests for
   the reference cores (Verilator, both `guarded` values, illegal use,
   `CLR`, mid-stream reset, every `BSV_*` macro combination the hand-written
   files honor); `-show-schedule` of a parameterized module; the existing
   `parameters/`, `noinline/`, `bsc.lib/fifo`, `bsc.bluesim/block_codegen`
   and `bsc.bluetcl/vcd_correlation` directories unchanged.
5. Verify: `make install-src`; `make localcheck` in the new directory and
   the directories above; full `make check` from `testsuite/` before
   reporting. Deliberate-break checks: remove `parameterized` and confirm
   T0043 returns; remove the proviso that decides a condition and confirm
   the undecidable-condition error names the condition; instantiate at
   width 0 and confirm the error.
6. Report: what changed (files, data types, new errors, new flags), the M0
   diff size, how to run the tests, the generated `FIFO2.v` next to the
   hand-written one, and anything you deviated from in this prompt and why.

## OUT OF SCOPE (do not do)

Per-instantiation specialization at the parent's elaboration (the sibling
design); width-generic C++ emission (`template <int width>` classes) in
Bluesim; payload polymorphism (`Bits a sa`) in the generated module;
schedule pinning and `savePortType` changes; replacing any primitive family
other than the FIFO2 pilot of M4; formal (LambdaCalc/SAL) output for
parameterized modules.

## ESTIMATE

M0 1000 to 2000 lines (mechanical and wide: the compiler points at every
site), M1 1000 to 1500, M2 1500 to 2500, M3 1000 to 2000, M4 a few hundred
plus library source: roughly 5000 to 8000 lines of Haskell before tests.
Most of that is not design risk: for a width-generic module the symbolic
widths do stay out of the way semantically, and the evaluator already lets
them fall through to residual applications; the cost is that `Integer`
widths are baked into ASyntax and some sixty to eighty back-end sites
compute with them (masks, extract bounds, concatenation merging, sized
literal printing, bit-vector sorts, zero-width tests), each needing the
same one-line "only if concrete" guard, with a missed site producing
silently wrong Verilog. M0's type change turns that audit into compile
errors, which is why it comes first. The Bluesim instantiation step is
self-contained (one substitution traversal plus naming) and adds no risk to
code generation.
