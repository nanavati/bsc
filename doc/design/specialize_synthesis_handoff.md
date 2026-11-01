# Handoff prompt: specialize size-polymorphic `synthesize` modules in bsc

This file is a prompt. Give it verbatim to an implementing agent. It is
self-contained; the agent needs no other conversation context. The longer
design document `doc/design/size_polymorphic_synthesis.md` is background
reading only; where the two differ, this prompt wins.

---

Implement per-instantiation specialization of size-polymorphic `synthesize`
modules in the Bluespec compiler (bsc), so that a polymorphic module marked
`synthesize` and `specialize` is synthesized once per distinct instantiation
as its own Verilog module and `.ba` file, compiled on demand from the
parent's elaboration.

## WHERE

Repository: the MatX fork of bsc, `matx-inc/bsc`, not upstream
`B-Lang-org/bsc`. This prompt was written against `matx-inc/bsc` branch
`main` at commit `99677cb` (2026-10-02, "CI: take the release GHC as a
dispatch input", the `release-2026.07.rc8` lineage; `.bo`/`.ba` format tags
`bsc-bo-20260715-6` / `bsc-ba-20260715-6`); `nanavati/bsc` `main`
(`941eecf`) is an ancestor of it. Work on a fresh branch off that commit,
or off the branch you are told to use. If you are told to target the
`release-frozen-A0` line instead (`fdd13b8`, 2026-10-20, the source of build
tag `build-20261023-1`), everything below still applies with one relocation:
the driver `src/comp/bsc.hs` lives at `src/comp/app/bsc.hs` there (program
entry modules moved under `src/comp/app`), the format tags are
`bsc-bo-20260715-14` / `bsc-ba-20260715-14`, and you must re-derive the next
free `Bin IdProp`/`Bin PProp`/`Bin IConInfo` tags from that tree's
`BinData.hs` and `GenBin.hs` rather than using the numbers quoted below.
Every other function, type and field named in this prompt exists on both
lines, and both carry the same fork features (lazy pack/unpack, `IATFCache`,
hash-consed `IType`, dictionary lifting, Integer module parameters, DPI
monomorphization, `-keep-inlined-boundaries`, `wiretypemap`).

Build and install with `make install-src` from the repository root (see
`INSTALL.md`; the result lands in `inst/`). Run tests from a testsuite
subdirectory with `make localcheck` (`testsuite/README.md`, "Running tests
in a subdirectory"); the suite picks up `inst/` automatically, or set
`TEST_RELEASE`.

FIRST read `DEVELOP.md` (compiler stages, Bluesim `-c` byte-identity mode,
conventions), `testsuite/README.md`, and section 3 of
`doc/design/size_polymorphic_synthesis.md` (the design this prompt
implements, with `file:line` citations; line numbers may have drifted, so
search by the function names given below; that document's 3.x subsection
numbers do not line up with this prompt's 3.x numbers).

Why this fork and not upstream: the files this feature touches have diverged
from upstream by about 2000 lines (`git diff --stat upstream/main -- src/comp/
IExpand.hs ...`: `IExpand.hs` +771, `IType.hs` +521, `FixupDefs.hs` +212,
`ISyntax.hs` 211, `bsc.hs` 186), the library work that motivates the feature
happens here, and the related upstream PRs by the same author (#999, #1022,
#1023, #1034) are still open. The feature itself does not depend on any
fork-only behavior, so keep it portable: put new logic in a new module
(`src/comp/Specialize.hs`), keep hooks in existing modules small, do not rely
on fork-only niceties such as lazy pack/unpack (`ICLazyPack`), compare and
print types through `pfpString`/structural equality rather than the fork's
hash-consed `IType` uniques, and thread the fork's `IATFCache` argument
wherever you call into `iExpand`/`genModule` (it is a parameter of both).

## WHY

bsc rejects `synthesize` on any module whose type has a proviso or a free
type variable: `Cannot synthesize 'mkFoo': Its interface is polymorphic.`
(T0043, `chkType` in `src/comp/GenWrap.hs`). The reason is structural: the
elaborator is a concrete-width partial evaluator (`type ASize = Integer` in
`src/comp/ASyntax.hs`; `PrimValueOf` on a non-literal numeric type is an
internal error in `src/comp/IExpand.hs`), so bsc cannot emit Verilog with a
`parameter width` that sizes ports and registers. The only size-polymorphic
synthesis boundaries today are the hand-written Verilog primitives
(`src/Verilog/FIFO2.v` with `parameter width`) imported through `import
"BVI"` / `module verilog`, with a parallel hand-written C++ model for Bluesim
(`src/bluesim/bs_prim_mod_fifo.h`).

The motivating goal is to replace those C++ models with reference Bluespec
implementations that both backends and the formal paths consume. For that,
a polymorphic reference `mkFIFO2 :: (Bits a sa) => Module (FIFO a)` must be
able to become a separate module per width, with a stable, predictable name,
without the user annotating each use site. The right shape is C++-template
style specialization: one monomorphic module per distinct instantiation.
Every backend already consumes exactly that shape; the Verilog module name
of an imported module is already an elaboration-time expression; and this
fork already monomorphizes polymorphic DPI functions per width. Upstream
issue B-Lang-org/bsc#921 asks for this and its maintainer's reply describes
the intended mechanism: elaborate the parent until a specializable submodule
is reached, stop, compile the submodule, come back.

## WHAT (what done looks like)

Given, in Classic syntax:

```
interface Q n =
    enq :: Bit n -> Action
    deq :: Action
    first :: Bit n

{-# verilog mkQ { specialize } #-}
mkQ :: Module (Q n)
mkQ = module ... -- any body

{-# verilog mkTop #-}
mkTop :: Module Empty
mkTop = module
    a :: Q 8 <- mkQ
    b :: Q 32 <- mkQ
    c :: Q 32 <- mkQ
    ...
```

or in BSV with `(* synthesize, specialize *)`, `bsc -verilog -g mkTop`
produces `mkTop.v`, `mkQ_8.v` and `mkQ_32.v`; `mkTop.v` instantiates
`mkQ_8 a(...)`, `mkQ_32 b(...)`, `mkQ_32 c(...)` with no `width` parameter;
`bsc -sim` produces the matching `.ba` files and Bluesim links them as
ordinary submodules; `-elab` writes the `.ba` files too. A specializable
module with a `Bits` proviso and a type variable (`(Bits a sa) => Module
(FIFO a)`), one written in BSV `module` syntax (`(IsModule m c) => m (FIFO
a)`), one with `parameter Bool guarded`, one with a static `Integer depth`
argument (3.4 below), one instantiated through `mapM`/`replicateM`/
`genWithM`, one instantiated inside a polymorphic parent, one at `Bit 0`,
one that instantiates another specializable module, and one defined in a
different package than its users all work. Monomorphic `synthesize` modules
behave exactly as before. `-u` does not loop. A `.bo` written by the new
compiler is readable by it (format tags bumped). All existing testsuite
directories stay green, including `testsuite/bsc.bluesim/block_codegen*`
(the `-c` byte-identity harness) and `testsuite/bsc.bluetcl/vcd_correlation`.

## CURRENT STATE (what exists, by function name)

Driver, `src/comp/bsc.hs`, `compilePackage`: parse → `genFuncWrap` →
`genWrap` → `mkSymTab` (rebuilt "because GenWrap added new types and
typeclass instances") → `addFuncWrap` → `derive` → `mkSymTab` →
`cCtxReduceIO` → `mkSymTab` → `cConvInst` → `cTypeCheck` → `simplify` →
`liftDictsPkg` → `iConvPackage` → load imports (`binmods`, `dictBuckets =
mkDictBuckets binmods`, `internalSymt <- mkSymTab errh mint`) → `fixupDefs
dictBuckets imod binmods` giving `imodf` and `alldefsList` → `iSimpDicts` →
`iSimplify` → `orderGens` → the `gen` fold over `ordgens :: [WrapInfo]`, which
for each module calls `genModule errh wi fwrapper flags dumpnames' prefix
(getIdBaseString pkgId) internalSymt alldefs elabATFCache (getDef im i')`
(this `getDef :: IPackage a -> Id -> IDef a` is a local closure inside
`compilePackage`, distinct from `GenWrap.getDef`), then `compileCDefToIDef
errh flags dumpnames' symt imods def` on the returned wrapper `CDefn`, then
`updDef dictBuckets idef im binmods` → `genUserSign errh symt mctx` /
`genEverythingSign errh symt mctx` (`mctx` is the pre-loop `CPackage`) →
`genBinFile`. Between `cTypeCheck` and `simplify` sit `genForeign` and
`genVPIWrappers`; `iConvPackage` also takes a `CATFCache`; `internalSymt <-
mkSymTab errh mint` where `mint = replaceImportedSignatures mctx impsigs'`.
`genModule` runs `iExpand errh flags symt alldefs atf_cache fwrapper pps def`
and the whole backend for one module, writes the `.v` and `.ba`, and returns
the wrapper `CDefn` built by `WrapInfo.deffun`. `compileCDefToIDef` wraps one
`CDefn` in a synthetic `CPackage`, context-reduces, typechecks against the
frozen `symt`, simplifies and `iConvDef`s it against the `IPackage` it is
handed: `iConvDef` builds its environment from that package's defs, and a
`CVar` found neither there nor in the symbol table becomes a bare `IVar`,
which `fixupDefs` cannot re-tie and the evaluator rejects with an internal
error. So any wrapper you compile for a specialization must be given the
extended symbol table *and* an `IPackage` that already contains the alias and
inner defs. Note the driver comment: the `gen` loop does not update
`alldefs`, and `internalSymt`/`symt` are fixed before the loop.

GenWrap, `src/comp/GenWrap.hs` (exports only `genWrap` and `WrapInfo(..)`):
`genWrap errh flgs genNames generating cpack symt` builds `ppmap :: Map Id
[PProp]` with `makePPropMap genNames pragmas` from the package's `CPragma
(Pproperties i pps)` plus `-g` names (`makeCmdLineGenPragmas`; `-g` names
exist only in this map and never reach the `.bo`), then runs `genWrapE` in
`GWMonad` (`runGWMonad ... (GenState errh symt flgs)`). `GenWrap.getDef`
finds the def among the current package's `CValueSign (CDef ..)` only
(`EUnboundVar` otherwise), runs `cCtxReduceDef` and `checkModuleArgPragmas`
on every def with pragmas, and for `generating && PPverilog` applies
`fixupPolyModType` (ties a *single* remaining `IsModule m c` predicate to
`Module`). `procDef`/`chkType` are the gate: proviso left → "It has a
proviso." (Classic: "context"); free type variables → "Its interface is
polymorphic."; "It is not a module."; polymorphic interface field; "not an
interface" (all T0043). Separately, `fixDef` replaces the body of every def
for which `isGenDef ppmap defid` holds (that is, `PPverilog` in the map) with
the placeholder `mkFoo = mkFoo`; it is keyed on the map, not on `getDef`'s
result. Per generated def GenWrap emits a flattened interface struct whose
id is built from the interface *type* (`flatTypeIdQual`/`flatTypeId`:
constructor and number names concatenated with no separator, `Q 8` → `Q8`,
`FIFO (Bit 32)` → `FIFOBit32`, plus always-ready tags and a soft-hyphen
`genSuffix` from `src/comp/GenWrapUtils.hs`; the function runs in `GWMonad`
over `CType` and is not exported), `to_`/`from_` defs, a `Generic` instance
(`mkTo_`, `mkFrom_`, `mkInstances`), an inner def `mkFoo<suffix>`
(`modIdRename`) of type `Bit n -> ... -> Module Foo_` under `Bits` provisos
whose body let-binds the user's def and applies it (`mkNewModDef`, `mexp =
cApply 10 (CVar i) exprs`), and a `WrapInfo { mod_nm, orig_cqt, wrapper_ifc,
wrapped_mod, wi_prags, deffun }` (the driver pattern-matches it positionally
with six fields; do not add fields). `deffun` (type `DefFun`, built by
`mkDef`) later produces the wrapper `CDef mkFoo orig_cqt [clause]` whose body
is `liftModule (xWrapperModuleVerilog fmod pps (CLit (LString
(getIdBaseString i))) ...)`, i.e. a `CmoduleVerilog` with `is_user_import =
False`, keeping the def's original (possibly `IsModule`-polymorphic)
`CQType`. Argument port and parameter names come from the clause binders
(`getDefArgs` in `GenWrapUtils.hs`, which keeps names only when there is one
clause with `CPVar` patterns and otherwise invents `_a1000`, `_a1001`, ...)
and argument-naming pragmas are checked against those names
(`src/comp/PragmaCheck.hs`, `checkArgName`, `EAttributeNoSuchArg`).
`genFuncWrap` (`src/comp/GenFuncWrap.hs`) is the precedent for fabricating
defs plus a `CPragma (Pproperties modId [PPverilog])` before GenWrap runs.

Evaluator, `src/comp/IExpand.hs` / `src/comp/IExpandUtils.hs`: `iExpand`
calls `runG errh flags symt alldefs atf_cache mi is_noinlined_func pps
(iExpandModuleDef def)`; `type G = StateT GState IO`; `GStateRO { errHandle,
symtab, defenv, checkMaxStep, maxStep, stepWarnInterval, flags }` is the
read-only part, `GState` the mutable part (`stateNo`, `stateNameMap`,
`stateLocMap`, heap pointer `hp`, `vars`, `portTypeMap`, `rules`, clock and
reset state, `defCache`), both fresh per `runG`; there is no global mutable
state beyond per-heap `IORef`s and the process-global `FString` and `IType`
intern tables (which only affect `Ord`, see 3.8). Pragmas are read inside the
evaluator with `getPragmas` (`IExpandUtils.hs`), a state field seeded from the
`[PProp]` passed to `iExpand`. After typecheck a variable use is `CApply
(CTApply f types) dictVars` applied to values (`tiVar` and `iAPs` in
`src/comp/TCheck.hs`), so an application's argument stack is type args (`T`),
then dictionary args (`E`, binders carry `IdPDict`, `isDictId` in
`src/comp/Id.hs`), then value args; `evalAp' (IAps f tys es) as = evalAp
"IAps" f (map T tys ++ map E es ++ as)`. `evalAp' (ICon i (ICDef t e)) as =
evalDef i t e as` (`step`, `cacheDef`, then `evalAp "ICDef"` on the body);
`evalAp' (ICon i ic) as = conAp i ic e as`; `conAp'` is the big
per-`IConInfo` dispatcher whose final clause is an `internalError`, so an
unhandled constructor fails loudly. Type application is beta-reduction
(`evalAp' (ILAM i k e) (T t:as)` via `evalApAccum`). `toHeap`/`toHeapCon`
(in `IExpandUtils.hs`) turn a bare `ICon i (ICDef t' e)` into its cached body
before heaping, so an unapplied module constructor passed as a value loses
its `ICDef` node. Type normalization inside `G` goes through `norm <-
getTypeNormalizerC` (over `fullTypeNormalizer :: Flags -> SymTab ->
IATFCache -> IType -> Changed IType`). `handlePrim` for
`ICVerilog` evaluates the module-name String expression (`evalString`) and
sets `vName` before `newState` creates the `IStateVar`; `PrimModuleBind`
names instances from the parent's binder through `IStateLoc`. `GOutput`
collects the module's state at the end of `runG`. `iExpandModulePortArgs`
turns a module argument into `ICModParam` (if `isParamModArg pps li`) or
`ICModPort`, and raises `EParamOnlyType` for an `Integer`/`String`/`Real`
argument without `parameter`; it runs only for the def being generated
(`iExpandModuleLam`).

Definitions and `.bo`, `src/comp/FixupDefs.hs`, `src/comp/GenBin.hs`,
`src/comp/BinData.hs`, `src/comp/IConv.hs`, `src/comp/GenSign.hs`:
`fixupDefs buckets ipkg binmods` concatenates the package's defs with all
imported packages' defs, merges pragmas (`nub`), and rewrites every `ICon i
(ICDef t _)` to point at the def body (`fixUp`), returning the package and
`alldefs`; `updDef` replaces one def and re-runs `fixupDefs`. The `.bo`
serializes `ipkg_pragmas` (package-qualified ids, `IConv.hs`) and every
`IDef` with its body; `ICDef` is written type-only and re-tied on load. `Bin
IdProp` and `Bin PProp` use explicit integer tags (`IdProp` last tag 38,
`PProp` last tag 35, both in `BinData.hs`); the `.bo` and `.ba` headers are
`bsc-bo-20260715-6` / `bsc-ba-20260715-6` (`GenBin.hs`, `GenABin.hs`) and
must be bumped on any format change. `genUserSign`/`genEverythingSign` run
over the pre-loop `CPackage`; `defExport` drops `IdPGeneratedIfc` ids from
both signatures. The `CSignature` keeps only `PPdeprecate` among pragmas.

Pragmas and parsers: `data PProp` in `src/comp/Pragma.hs` (`PPverilog`,
`PPparam [Id]`, `PPCLK`/`PPRSTN`, argument-name pragmas such as
`PParg_port`, `PPclock_osc`, method-name pragmas such as `PPalwaysReady`);
Classic module pragma syntax `{-# verilog mkFoo { parameter g, reset_prefix =
"RST", ... } #-}` parsed by `pPragma`/`pVeriGenProps` in
`src/comp/Parser/Classic/CParser.hs`; BSV attributes in
`src/comp/Parser/BSV/CVParser.lhs` (the `allowed` list that starts with
`"synthesize", "always_ready", ...` and the `case getIdString name of
"synthesize" -> numeric PPverilog name` dispatch).

Dependencies and link: `src/comp/Depend.hs` `getPkgInfo` puts every
`PPverilog` def id into `gens`, and `getGenFs` expects `<gen>.v`/`.ba` to
exist (a listed-but-missing file forces a rebuild every `-u` run, as its
comment about DPI wrappers explains). `src/comp/ABinUtil.hs`
`getABIHierarchy`/`followABMIHierarchy` partition submodule instances by
`avi_user_import`: a non-user-import instance is followed by name and
`<name>.ba` is read from the `-p`/`-bdir` path (`findABI`,
`readAndCheckABinPath`, which looks for `<name>.ba` and checks that the
`apkg_name` stored in it equals the name it was looked up by,
`EABinNameMismatch` otherwise); a user import whose name is not a Bluesim
primitive is `EBSimForeignImport` regardless of `.ba` presence. Bluesim, bluetcl and the LambdaCalc/SAL
backends match primitives by exact `vName` string
(`src/comp/SimPrimitiveModules.hs`, `src/comp/LambdaCalcUtil.hs`).

Zero width: the backend never emits zero-width ports or defs
(`isNotZeroSized` in `src/comp/AVerilog.hs` and `src/comp/AVerilogUtil.hs`);
`testsuite/bsc.lib/fifo/depth_param/` already runs a synthesized zero-width
FIFO under both backends.

## DESIGN (decided; deviate only with a reason stated in your spec)

### 3.1 Pragma

New `PProp` constructors `PPspecialize` and `PPverilogName String`. Classic:
`specialize` and `verilog_name = "..."` inside the `{-# verilog m { ... }
#-}` brace list (`pVeriGenProps`). BSV: `specialize` and `verilog_name`
attributes next to `synthesize`. Add `Bin PProp` cases (next free tags) and
bump both headers. A def is **specializable** iff it carries `PPverilog` and
`PPspecialize`. Behavior for defs without `PPspecialize` is unchanged,
including today's T0043 errors.

### 3.2 GenWrap

In `GenWrap.getDef`/`chkType`, for a specializable def when `generating`:
do not create a `WrapInfo`, and exclude the def from `isGenDef` as well (or
guard `fixDef` with `PPspecialize` absent) so its body is not replaced by the
`mkFoo = mkFoo` placeholder; the def stays exactly as written. Before
classifying, strip `IsModule` from a multi-predicate context
(`fixupPolyModType` only handles a single predicate). Keep erroring on the
gates that type arguments cannot fix: polymorphic interface *fields*,
non-interface result, non-module type, interface or function arguments.
`-g mkFoo` on a specializable def is a new error: "`mkFoo` is specialized per
instantiation; instantiate it from a synthesized module or give it a
monomorphic alias." The merged `[PProp]` does not record whether `PPverilog`
came from `-g` or from source, so detect this by checking the def's name
against `genNames` (thread `genNames` into `genWrapE`, or test in `genWrap`
before `makePPropMap`). Since the `specialize` pragma is a source `CPragma`,
it reaches `ipkg_pragmas` with a package-qualified id and importers can find
it; the registry scan over all loaded packages must dedupe (each `.bo`
repeats its imports' pragmas).

`Depend.hs` `getPkgInfo`: exclude specializable defs from `gens`.
`bluetcl.hs` `defs module`: exclude them too (search for the `PPverilog`
filter near the `"module"` subcommand).

### 3.3 Evaluator node

Add to `data IConInfo a` in `src/comp/ISyntax.hs`:

```
| ICSpecDef { iConType  :: IType       -- the def's scheme
            , specKey   :: Id          -- qualified def id
            , specNTy   :: Int         -- number of leading type args
            , specNDict :: Int         -- number of leading dictionary args
            , specStat  :: [Int]       -- 0-based positions of static args among value args
            , specBody  :: IExpr a }
```

`fixupDefs` installs it (instead of `ICDef`) for every reference to a def in
the specializable set, derived from the merged pragma list (the install and
re-tie point is `FixupDefs.fixUp`'s `ICon i (ICDef t _)` clause; add the
`ICSpecDef` case there and re-tie `specBody` for nodes read from a `.bo`).
The build uses `-Wall`, so every exhaustive `IConInfo` dispatcher needs a
clause. Sites that must gain one: `ISyntax.hs` `ordC` (new number), `cmpC`,
the `rnf` instance (same no-descent treatment as `ICDef`, bodies are
cyclic), `showTypelessCI`, `fdVars'` (return the id, as for `ICDef`; the
driver's `orderGens` and `ISimplify` depend on it), the `PDReadable`
`pPrint` case; `GenBin.hs` `Bin IConInfo` (`ICDef` is tag 0, written
type-only and read back as an undetermined body; use the next free tag,
currently 20, writing type, key, arities and static positions); `IExpand.hs`
`rmConInfo`; `ISyntaxSubst.hs` `etSubstIConInfo` (an explicit no-op clause
like `ICDef`'s); `ISimplify.hs` `isTriv`, `dVars'` and its local `fixUp`.
Sites that must *not* gain one, because matching only `ICDef` is the point:
`ISimplify.expDef` (never inlined), `toHeap`/`toHeapCon` (an `ICon` with
`ICSpecDef` falls to the generic `ICon` clause and is heaped as itself, never
as its body), `evalAp'` (so it reaches `conAp'`). `ISyntaxUtil.hs` and
`ISyntaxCheck.hs` contain no `ICDef`-specific code and need nothing.

In `conAp'`: treat `ICSpecDef` as a fixed-arity primitive. Accumulate `T`
and `E` arguments into a WHNF partial application (`IAps (ICon i info) tys
es`) until `specNTy` type args, `specNDict` dictionaries and every static
position in `specStat` are present. Only then:

1. Partition the type arguments. Those bound by the def's `IsModule m c`
   proviso (identify them from the scheme: the predicate's type variables)
   are *not* part of the key. Normalize the others with the `G`-monad
   normalizer (`norm <- getTypeNormalizerC`); any that is not fully concrete
   (`ITVar` or an unevaluated type function) is a user error at the
   application position:
   "type arguments of specializable module `mkFoo` could not be
   determined". Evaluate each static argument to a literal with
   `evalInteger` / `evalString` (add a small `ICReal` case for `Real`); a
   non-literal, including a parent `ICModParam`, is an error.
2. Key = (qualified id, kept type args, static values). Name = `mangle`
   (3.6).
3. If key == the specialization currently being generated
   (`g_current_spec :: Maybe SpecKey`, new `GStateRO` field): evaluate the
   body inline (`evalDef`-style on `specBody` with the full stack). The
   alias's inner def is `let mkQ_32 = \args -> mkQ @32 ... in mkQ_32 ...`,
   so every specialization reaches its own key exactly once; this is
   expected, not a cycle. If key is on the active generation stack
   (`g_spec_stack :: [SpecKey]`) but is not the current one, it is a cycle:
   error naming the chain. No fixed depth limit.
4. Look the name up in the registry (`g_registry :: IORef (Map String
   (IDef HeapData))`, holding each wrapper's fixed-up *top-level* def as it
   sits in `ipkg_defs`/`alldefs` after `fixupDefs`; such a body is heap-free
   by construction). Never store a heaped value: `HExpr` may contain `IRefT`
   heap pointers that are only valid inside one `runG`, and each child
   compile is its own `genModule`/`runG` with its own heap. On a miss, call
   `g_specialize key` (a callback in `GStateRO`, `SpecKey -> IO (IDef
   HeapData)`) which compiles the child (3.5), inserts the wrapper and
   returns it.
5. Redirect: read the wrapper def's type and apply one `T` argument per
   leading `ITForAll` binder (`m` and `c` when the def was
   `IsModule`-polymorphic, none when its type was already `Module ...`) and
   one `E` argument per leading dictionary arrow, taken from the saturated
   stack in order; then the remaining value arguments with the static
   positions removed; then continue with the rest of the stack. Do not
   hard-code the arity: the wrapper keeps `orig_cqt`, so its binder order is
   whatever the scheme says after context reduction and typecheck.
   `clocked_by`/`reset_by` wrap the *result* of the module expression, so
   nothing special is needed; instance naming comes from the parent's binder
   as for any submodule.

Why a node and not a check in `evalAp'`'s `ICDef` clause: module
constructors are routinely passed unapplied (`mapM mkFoo xs`, `genWithM`,
`replicateM`), heaped by `toHeap`, and forced later with an empty stack; a
check in the `ICDef` clause would see only the type arguments or nothing and
silently inline, losing the boundary.

### 3.4 Static arguments

For a specializable def, an `Integer`, `String` or `Real` argument *without*
`parameter` is a static argument (3.3 step 1). With `parameter` it is a
Verilog parameter exactly as today (this fork supports `Integer`
parameters). Static positions are found from the def's type, in order, and
may be interleaved with `Clock`, `Reset` and port arguments. Arguments of
interface, function or `Module` type are a definition-site error.

### 3.5 Child compile (`g_specialize`)

1. **Alias.** Build a `CDef` named `mangle key`, in clause form, reusing the
   def's own `ILam` binder names for the non-static arguments
   (`mkQ_32 guarded = mkQ guarded`; never point-free: `getDefArgs` would
   invent names and every argument pragma would fail
   `EAttributeNoSuchArg`). Its `CQType` is built from the def's scheme
   (`findVar :: SymTab -> Id -> Maybe VarInfo` yields an `Assump` `i :>:
   Scheme`, not a `CQType`; instantiate the scheme's quantified variables)
   with the kept type variables substituted by `iToCT` of the key's types
   (`iToCT :: IType -> CType` in `IType.hs`; it internal-errors on
   `ITForAll`, so apply it to the concrete argument types only), the
   specialized provisos dropped, and the static argument positions removed.
   Its body applies `CVar mkFoo` to literals at the static positions and to
   the binders elsewhere. Copy the def's
   module-level `Pproperties` onto the alias minus `PPspecialize` and
   `PPdeprecate`; this single list is what GenWrap's `ppmap`,
   `WrapInfo.wi_prags`, IExpand's `getPragmas`, AConv and `abmi_pps` all
   read.
2. **Round pipeline.** Put the alias and its pragma into a synthetic
   `CPackage` that also holds the current package's type, class and
   instance declarations, the value signatures the alias needs (`mkFoo`'s
   type, so the alias typechecks against it) and the import signatures, and
   run the same sequence the driver runs: GenWrap → `mkSymTab` → `derive` →
   `mkSymTab` → `cCtxReduceIO` → `mkSymTab` → `cConvInst` → `cTypeCheck` →
   `simplify` → (`liftDictsPkg` if enabled) → `iConvPackage`; merge the
   resulting `IDef`s and declarations into the current `IPackage`; run
   `fixupDefs`. `genWrapE` is not exported and runs in `GWMonad`, and the
   `IfcTRec` list it builds (`trs`/`finalIfcTRecs`) is internal: add an
   exported IO entry point to `GenWrap.hs`, for example
   `genWrapWithPPropMap :: ErrorHandle -> Flags -> M.Map Id [PProp] -> (Id
   -> Bool) -> CPackage -> SymTab -> IO (CPackage, [WrapInfo])`, whose
   predicate says "this flattened-interface id already exists" and is
   applied to the `IfcTRec`s before `genTDef`/`mkTo_`/`mkFrom_`/
   `mkInstances`. `compileCDefToIDef` alone is not enough: GenWrap adds a
   struct, a `Generic` instance and conversion defs that the symbol table
   must know before the inner def typechecks (the wrapper's method types are
   computed from the symbol-table entry of the flattened interface in
   `IConv.hs`). Batch every key demanded in one round into one synthetic
   package, and skip `IfcTRec`s whose flattened-interface id already exists
   in the package or symbol table: those artifacts are named from the
   interface *type*, so two specializations with the same result type would
   otherwise collide (`EMultipleDecl`, `EDuplicateInstance` in
   `MakeSymTab.hs`). From then on thread the extended symbol table, the
   extended `IPackage` and `alldefs` into every later `genModule` and
   `compileCDefToIDef` call (store them in `IORef`s owned by the driver;
   today all are fixed before the `gen` loop).
3. **Generate.** Run `genModule` on the inner def with `g_current_spec =
   Just key` and the key pushed on `g_spec_stack`; it recursively
   specializes grandchildren through the same callback, writes the child's
   `.v` and `.ba`, and returns the wrapper `CDefn`. `compileCDefToIDef` the
   wrapper with the extended symbol table and the `IPackage` that already
   contains the alias and inner defs (see CURRENT STATE on `iConvDef`'s
   environment), tag its id `IdPSpecialization` (new `IdProp`, `Bin IdProp`
   tag 39), `updDef` it into the package, insert its fixed-up def into the
   registry.
4. **Visibility.** The new defs are created after the signatures were
   computed, so they are in neither `bi_sig` nor `bo_sig` and reach
   importers only through `ipkg_defs`/`alldefs`. Extend `defExport` in
   `GenSign.hs` to also drop `IdPSpecialization` ids so that any later
   signature regeneration (bluetcl `bpackage` commands) does not surface
   them.

### 3.6 Naming

`mangle :: Id -> [IType] -> [static value] -> String`. Base = `verilog_name`
if present, else the def's base name. Append `_<arg>` per kept type argument
and static value, flattening each `IType` the way GenWrap's `flatTypeIdQual`
flattens a `CType` (constructor and number names concatenated) but as a
small pure function over `IType` in `Specialize.hs` (`flatTypeIdQual` is not
exported, runs in `GWMonad` and takes `CType`): `ITNum n` → decimal; `Bit
32` → `Bit32`; `Bool` → `Bool`;
`Integer` static → decimal (negative as `m<n>`); `String` static → the string
if it is a legal identifier fragment, else hashed. If the result exceeds 64
characters or any argument needed character replacement, use `<base>__h<16
hex digits>` of a hash of the canonical `pfpString` of (qualified id, types,
statics); never hash pointer identities or `IType` uniques. The key is the
full type-argument list, not the widths they imply. Because the alias def is
*named* by the mangled string, the wrapper's Verilog name literal
(`getIdBaseString i` in `mkDef`), `apkg_name` (`AConv.hs`), the `.v`/`.ba`
file names (`modstr` in `genModule`/`writeABin`) and Bluesim's lookup by
`vName` all agree without further plumbing. Reject a `verilog_name` equal to
a current Bluesim primitive name (`isPrimitiveModule`), since Bluesim,
bluetcl and the formal tables match primitives by exact name.

### 3.7 Registry and cross-package reuse

Registry = `Map String HExpr` seeded at the start of `compilePackage` from
every loaded package's `ipkg_defs` whose id carries `IdPSpecialization`,
plus what this compile generates. Reuse therefore requires the using package
to import, transitively, the generating one; siblings regenerate identical
modules. Outputs go to `-vdir`/`-bdir` like any synthesized module. Record,
in the user documentation you add, the existing link-time facts: `.ba` found
by name on the path; modules discovered during the hierarchy walk are deduped
by name; two same-name `.ba` *listed* on the link line are an error
(`EMultipleABinFilesForName`); the same name in two path directories takes
the first with a warning; the same `-bdir` is silently overwritten; a `.ba`
from a Verilog compile cannot be linked by Bluesim (`EABinFileBackendMismatch`).
Specializations are compiled with the compiling package's flags in this
version; `abmi_flags` is already stored in the `.ba`, so a later change can
compare profiles at link. Treat specialization outputs like this fork's DPI
wrappers for `-u`: regenerated whenever the generating package compiles,
not tracked by `Depend.hs`.

### 3.8 Determinism

`Ord FString` compares intern ids, `Ord Id` compares `FString`s, and `Ord
IType`/`Ord IExpr` are structural over those `Id`s (the `IType` hash-cons
uniques are never used for ordering), so map-ordered intermediate structures
can differ between "child compiled during the parent" and "child reused from
a `.bo`". The invariant to test is "same
result as compiling the child before the parent in the same process", the
property today's multi-module `gen` loop already has: add a test that diffs
the child's `.v` and `.ba` between a compile that generates it and a compile
that reuses it from an import.

## CONSTRAINTS

- Monomorphic `synthesize` modules must produce byte-identical `.v` and
  `.ba` before and after your change (compare on `testsuite/bsc.verilog`
  and `testsuite/bsc.bluesim` expected files; the suite enforces most of
  it).
- No changes under `src/bluesim/`, `src/Verilog/` or `src/Libraries/` except
  test inputs under `testsuite/`. No library primitives are replaced in this
  task.
- Any `.bo`/`.ba` format change (new `IdProp`/`PProp`/`IConInfo` tags) bumps
  both header tags in `GenBin.hs` and `GenABin.hs`.
- Keep `testsuite/bsc.bluesim/block_codegen`, `testsuite/bsc.bluesim/
  block_codegen_sweep` (`-c` byte-identity) and
  `testsuite/bsc.bluetcl/vcd_correlation` green; specialized modules are
  ordinary submodules to both.
- The compiler builds with `-Wall` (`src/comp/Makefile`), so incomplete
  pattern matches on `IConInfo` are warnings you must clear, not ignore; see
  the site list in 3.3.
- New logic lives in `src/comp/Specialize.hs` (key, `mangle`, alias
  construction, round pipeline driver, registry); hooks in `IExpand.hs`,
  `IExpandUtils.hs`, `GenWrap.hs`, `FixupDefs.hs`, `bsc.hs`, `Depend.hs`,
  `Pragma.hs`, `BinData.hs`, parsers and `Error.hs` stay as small as the
  design allows, so the feature can be ported to upstream bsc (issue #921).
- Haskell as the repository writes it: no new package dependencies, GHC
  warnings clean, existing `internalError` conventions, error messages added
  in `src/comp/Error.hs` with new numbers in the existing scheme.
- On any unsupported situation fail with a clear user error at a source
  position; never silently inline a specializable module (the one place that
  previously would have, unsaturated higher-order use, is now impossible by
  construction of the node; if you find another, make it an error).
- Do not open pull requests, do not push to any branch other than the one
  you were given, do not modify upstream remotes.

## APPROACH

1. Explore the code paths named above; confirm every function name and
   adjust where the tree has moved on.
2. Write a design spec to `doc/design/specialize_synthesis_spec.md`
   covering: exact data-type changes, the `conAp'` saturation logic with
   the argument-stack invariant, the alias construction with one worked
   example (`mkFIFO2`-like with a `Bits` proviso, a `parameter Bool`, and a
   static `Integer`), the round-pipeline function signatures, how the symbol
   table and `alldefs` are threaded, the registry life cycle, error list,
   and the test list. Commit it and return it for review **before** writing
   compiler code.
3. After approval, build in this order, each step green before the next:
   - M0 spike: `ICSpecDef` + `fixupDefs` installation + `conAp'` saturation
     that *inlines* (no redirect yet) and traces the keys it computes under a
     hidden `-trace-specialize` flag; verify on tests with `mapM`,
     `replicateM`, `genWithM`, partial application in a `let`, and a
     polymorphic parent that every instantiation is intercepted exactly once
     with the right key.
   - M1 pragma, parsers, `Bin` tags, header bumps, GenWrap gate changes,
     `Depend.hs` and bluetcl exclusions, new errors.
   - M2 alias construction and the round pipeline for one key; child
     compile and redirect; the two-width example works under `-verilog`
     and `-sim`.
   - M3 `IsModule` handling (BSV `module` syntax parent and child,
     `ModuleContext`), static arguments, `parameter` arguments.
   - M4 registry across packages, `IdPSpecialization`, `defExport`, the
     determinism diff test.
   - M5 batching and flattened-interface dedup, nested and recursive
     specializations, cycle detection, zero width.
   - M6 diagnostics, user-guide text (`doc/user_guide/user_guide.tex`, the
     `synthesize` attribute section, LaTeX), `verilog_name`.
4. Tests, in a new `testsuite/bsc.verilog/specialize/` (a sibling of
   `noinline/` and `parameters/`; `testsuite/bsc.synthesize/` is the suite
   for the unrelated `-synthesize` gate-level flag) with a `Makefile` copied
   from `testsuite/bsc.verilog/noinline/Makefile` and a `specialize.exp`
   using the suite's existing procedures (`compile_verilog_pass`,
   `test_c_veri_bsv_modules`, `find_regexp` on generated `.v`,
   `compile_fail_error` or `compile_verilog_fail_error` with the new error
   numbers): the two-width example
   (expected `.v` names and instantiations, no `width` parameter); BSV
   `module`-syntax and `ModuleContext` parents; higher-order uses; static
   argument interleaved with a `Clock` argument, and the dynamic / parent-
   `parameter` static-argument errors; `parameter [0 : 0] guarded = 1'b0;`
   in the child and `.guarded(1'd1)` at the instance; `Bit 0`; nested
   specializable modules; a 100-stage recursive `mkTree n`; a genuine cycle;
   two specializations sharing one result type; a specialization sharing
   its result type with a monomorphic synthesized module; cross-package
   with and without the transitive import; `verilog_name`; Bluesim
   co-simulation with `-keep-fires`; `-c` byte-identity over the generated
   specializations; `-g` on a specializable def; unresolved type argument;
   the existing `noinline` polymorphic error (T0111) still fires
   (`testsuite/bsc.verilog/noinline/`).
5. Verify: `make install-src`; `make localcheck` in the new directory and
   in `testsuite/bsc.verilog/parameters`, `testsuite/bsc.verilog/noinline`,
   `testsuite/bsc.lib/fifo`, `testsuite/bsc.bluesim/block_codegen`,
   `testsuite/bsc.bluetcl/vcd_correlation`, `testsuite/bsc.codegen`; then
   a full `make check` from `testsuite/` before you report. Deliberate-break
   checks: remove `specialize` from the pragma and confirm T0043 returns;
   introduce a cycle and confirm the cycle error names the chain; pass a
   register value as a static argument and confirm the error.
6. Report: what changed (files, data types, new errors), how to run the
   tests, the Phase-1 cost you measured (compile time of the two-width
   example with and without specialization), and anything you deviated from
   in this prompt and why.

## OUT OF SCOPE (do not do)

Replacing any Bluesim C++ primitive or Verilog library module; schedule
pinning; `savePortType` changes; `-prim-impl`; the specialization manifest
for build systems; canonical flag profiles; instantiation-site
`(* synthesize *)`; upstream porting. These are later work items that build
on this one.
