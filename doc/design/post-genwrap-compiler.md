# A Post-GenWrap Bluespec Compiler

## Boundary contracts, specialization-first synthesis, and library-defined wrapping

*Consolidated design, 2026-07-02; revised 2026-07-03 with the
contract/binding factoring (§3.1.1, A15), the interpreted port-annotation
split and SV-typed ports (§5.1, A16), and the b2r / typed-waveform-decoding
assessment (Appendix B). Synthesizes the BVI-fallback implementation
experience (v1, shipped on a downstream branch), the subsequent design
discussion, the "Longer-Horizon Bluespec Projects" cross-check, the
MatX-inc/matx issue sweep, and the full B-Lang-org/bsc issue sweep (375
issues, open + closed). All file:line citations were verified against
B-Lang-org/bsc `main` at commit `534241d`.*

---

## 0. Executive summary

The synthesis boundary — the place where an elaborated BSV module becomes a
Verilog module or a Bluesim object, and where a parent compilation trusts a
child's ports and schedule — is the most load-bearing concept in bsc, and it
has no representation in the compiler. It exists only as the *side effects* of
five phases: BVI parsing, GenWrap's pre-typecheck rewriting, elaboration-time
pragma consumption, post-schedule wrapper assembly, and parent-side trust of
declared schedules. GenWrap (`src/comp/GenWrap.hs`, 2299 lines) is where the
pain concentrates: it runs *before* the typechecker but does type-level work,
so it maintains a shadow type system that cannot handle interfaces computed by
type functions, duplicates interface flattening that is re-implemented at
least four times across the tree, and accepts boundary requirements only in
the shape of surface pragmas.

This document proposes a compiler organized around three ideas:

1. **The boundary contract as a first-class object** with two modes — *infer*
   (today's synthesis: elaborate a module, fill in its `VModInfo`) and
   *target* (give the compiler a required boundary — from a BVI import, a
   declared-schedule attribute, or a previous `.ba` — and have it verify the
   module against it after scheduling). BVI imports, BVI fallbacks,
   polymorphic specializations, declared schedules, and schedule regression
   pinning all become the same mechanism.

2. **Specialization-first polymorphic synthesis.** A polymorphic
   `(* synthesize *)` module is *defined* by its family of monomorphic
   specializations, each an ordinary run of today's backend. Specializations
   are demanded during parent elaboration, keyed by the instantiation's type
   vector plus resolved-dictionary hashes, memoized in memory and in the
   `bdir`. Width-generic netlists, content-hash deduplication, and shared
   front-ends are *compression rungs* over this ground truth, never the
   semantics.

3. **Library-defined boundary translation; a one-application injection.**
   Finish the migration that `WrapField`/`SplitPorts` started: enrich the
   generic `Rep`/`Meta` representation so interface flattening, port naming,
   and ready/enable handling become ordinary generic programs, and shrink
   GenWrap's code injection to a single typechecked application per boundary
   (`mkFoo = wrapModule contract mkFoo_`). Boundary translation then has
   three library-defined levels — field (`WrapField`), port (`SplitPorts`),
   monad (`Expose`/`Hide`) — and the compiler keeps exactly three jobs: mark
   the boundary, supply the primitives, fill-or-verify the contract after
   scheduling.

The migration is a sequence of independently shippable wedges, not a rewrite.
Each wedge is motivated by, and closes, concrete issues from the B-Lang-org
tracker; the sweep results are folded in throughout and tabulated in §8.

---

## 1. Background: what exists today

### 1.1 The pipeline and GenWrap's position in it

The static-elaboration pipeline in `bsc.hs` runs, per package:

```
parse → mkSymTab → genFuncWrap → GenWrap (bsc.hs:384)
      → symtab rebuild (bsc.hs:387-391) → deriving → ctxreduce → convinst
      → typecheck (bsc.hs:428)
      → .bo/.bi emission
per synthesized module (genModule, bsc.hs:656):
      iExpand (bsc.hs:696) → transformations → aSchedule (bsc.hs:825)
      → AAddScheduleDefs / AAddSchedAssumps → backend:
        Verilog:  aState (bsc.hs:1092) → aVerilog (bsc.hs:1176)
        Bluesim:  simExpand (bsc.hs:1281) → C++ blocks
```

GenWrap runs five phases *before* the typechecker. Its job: for each
`(* synthesize *)` module, mint a flattened, bit-level interface type; rewrite
the module to produce that type; and record a `WrapInfo` whose `deffun`
continuation (`GenWrap.hs:148`, built by `mkDef` at `GenWrap.hs:1456-1459`)
will later — after scheduling — generate the user-facing wrapper that converts
the synthesized boundary back to the original polymorphic interface.

### 1.2 The diagnosis: a phase in the wrong place, doing work it cannot do

GenWrap does type-level work without the typechecker:

- It maintains **its own synonym expansion and type equality**: "GenWrap
  defines its own versions that expand synonyms and use qualEq"
  (`GenWrap.hs:39-41`); `expandSynSym` (`GenWrap.hs:1851`) is called ~15
  times; a self-flagged wrongness at `GenWrap.hs:1784`: "XXX use of `qualEq`
  is wrong".
- It derives the interface **syntactically**: `ifcNameFromMod`
  (`GenWrap.hs:638`) applies `getArrows` to the unnormalized module type.
  Any interface position that requires actual type computation — a type
  synonym family, a type-level function producing the ifc — is invisible to
  it. This is the root cause of the "interfaces computed by type functions
  don't synthesize" failure class.
- It **flattens interfaces by string mangling**, and admits it does so twice
  internally: `flattenFInfs` (`GenWrap.hs:710`) with the comment "XXX This
  flattening is redone in genIfcFieldFN" (`GenWrap.hs:708-709`). The same
  prefix-flattening traversal is re-implemented in `IExpandUtils.hs`
  (boundary names, lines 1514-1585), in `bluetcl.hs` (introspection), and in
  `SymTab.hs:392` / the BVI parser (`CVParser.lhs:2988-3013`) — four-plus
  copies of one semantic operation, coupled only by the `mkUSId`/`flattenUSId`
  string primitives (`Id.hs:442-448`).
- It **leaves the symbol table stale** ("XXX we don't update the symbol table
  with the new instances / XXX we rely on the symbol table being rebuilt",
  `GenWrap.hs:354-355`), forcing the rebuild at `bsc.hs:387-391`.
- Boundary *requirements* can enter only as **surface pragmas**: naming
  reaches elaboration via symtab `FieldInfo` distilled into `IfcBetterInfo`
  (`IExpand.hs:958-970`, `IfcBetterInfo.hs` — a module whose own header says
  "this package needs re-thinking", `IfcBetterInfo.hs:33-34`). There is no
  input channel for "make the boundary look exactly like *this*" other than
  encoding it as pragmas — which is exactly what the v1 fallback
  implementation had to do (§2).
- Known breakage sits unfixed at the seams: "XXX: alwaysEnabled is dropped
  and broken (not propagated to {inhigh})" (`GenWrap.hs:1455`); the
  `AState.hs:409-412` wish to "use the fieldinfo to create the right names
  (and ARenameIO goes away)".

Meanwhile the *output* side of the boundary is in good shape and must be
preserved: `VModInfo` (`VModInfo.hs:561-569` — `vName`, `vClk`, `vRst`,
`vArgs`, `vFields`, `vSched`, `vPath`) is **width-free**: `VArgInfo` and
`VFieldInfo` carry names, clock/reset association, and port protocol, never
bit widths (`VModInfo.hs:178-185`, `270-286`). Everything downstream of
scheduling — parent elaboration (`ICVerilog { vInfo, vMethTs }`,
`ISyntax.hs:774-777`; instantiated at `IExpand.hs:1377-1408` via `newState`),
parent scheduling (which trusts each submodule's declared `VSchedInfo`
verbatim: `ASchedule.hs:1710-1712`, `2779`, `4420`), and both backends — reads
*only* per-instance `VModInfo`. This is the single most load-bearing lesson
from the fallback work: **backends and parents need zero changes for any of
what follows**, because the design never asks them to read anything but
`avi_vmi`.

### 1.3 The half-finished migration: WrapField / SplitPorts

The boundary-conversion *semantics* have already half-moved into the library,
via typeclasses over the derived generic representation:

- `WrapField` (`Prelude.bs:4619`): `class WrapField name f w | name f -> w`,
  with `toWrapField`/`fromWrapField`/`saveFieldPortTypes`. GenWrap emits a
  fresh type variable and a `WrapField` constraint and lets the solver
  compute the wrapped type (`GenWrap.hs:907-921`) — the class side already
  owns representation conversion.
- `WrapMethod` (`Prelude.bs:4663`) peels method arguments one at a time
  (`Prelude.bs:4679`), computes port names, and — notably — reports its
  errors **at elaboration time** via `primError (getEvalPosition prx)`
  (`Prelude.bs:4707`, `4718`, `4776`).
- `SplitPorts`/`ShallowSplitPorts`/`DeepSplitPorts` (`Prelude.bs:4781`,
  `SplitPorts.bs:32-156`) do per-argument port explosion as generic programs
  over `Rep`/`Meta`/`Conc` (`Prelude.bs:4537-4569`), walking `MetaField` to
  compose port names (`SplitPorts.bs:66`).
- Names and types flow to the backend through primitives: `primMethod`
  (`Prelude.bs:4614` → `IExpand.hs:3170`) and `primSavePortType`
  (`Prelude.bs:2593` → `IExpand.hs:1410`).

This migration has history and momentum upstream: it was proposed as issue
#714 ("Better control of wrapper generation", krame505's `Wrapped`-typeclass
sketch) and landed as PR #729 (merged 2026-03-31). Its first fallout issues
are field reports on exactly the residues this design must fund: #899
(port-name-collision error positions degraded once names are computed in the
evaluator), #900 (spurious `T0031` from a `WrapField` context failure
alongside the real error), and #901 (the `AppendTuple` helper class cannot
take bidirectional fundeps — instance overlap becomes unorderable, `T0128`).
#714's own open uncertainties — how to carry interface-field pragmas, whether
to add a `MetaIfc` — are precisely the enriched-`Rep` design of §5.1.

What remains on the Haskell side is precisely the **pre-typeclass residue**:
`ifcNameFromMod`'s syntactic ifc derivation, `flattenFInfs` string
flattening, `IfcTRec`/`genTDef` minting the nominal flattened tycon
(`GenWrap.hs:174`, `825`), `RDY_` string mangling, and `deffun` stub
assembly. Each has a demonstrated class-side analogue — `ShallowSplitPorts'`
walking `Meta`/`Conc` *is* flattening. The migration stopped halfway, and the
fighting happens at the seam.

One structural fact explains why it stopped where it did. **GenWrap injects
code whose types it cannot compute** — the `WrapField` fundep exists because
only the constraint solver knows the wrapped type `w` — so the injection must
precede typechecking. That is the load-bearing circularity that pins GenWrap
before TCheck, and dissolving it (not patching around it) is the endgame of
§5.

### 1.4 Existing degenerate cases of "declared and verified boundary"

The design below generalizes machinery bsc already has in miniature:

- `always_ready`/`always_enabled` are **declared-and-verified boundary
  micro-contracts**: `AAddScheduleDefs.hs:190-197` emits a `ProveEq e aTrue`
  proof obligation for each declared-always-ready method; failure is the
  `ENotAlwaysReady` error unless downgraded by `-unsafe-always-ready`
  (`FlagsDecode.hs:1617-1619`).
- `genC`/`genVerilog` are elaboration-time backend selectors (`PrimGenC` /
  `PrimGenVerilog`, `IExpand.hs:3910-3925`), injected into the Prelude by
  `bsc.hs:476-489` (self-critically: "should probably be done via
  primitives"). Both **taint** the module as backend-specific
  (`setBackendSpecific`) — the mechanism this design deliberately obsoletes
  for the IP-substitution use case (§2) and eventually for zero-width
  dispatch (§6).
- Reentrant elaboration mid-compile already exists: `AAddSchedAssumps.hs`
  runs a nested `runTI` → `iConvExpr` → `iExpand` → `aConv` to elaborate an
  RWire during a parent's post-scheduling pass
  (`AAddSchedAssumps.hs:221-239`). This is the precedent that makes nested,
  demand-driven specialization (§4) credible rather than speculative.
- The library hand-maintains what §6 mechanizes: zero-width Verilog variants
  (`FIFO10.v`, `SizedFIFO0.v`, `RWire0.v` in `src/Verilog/`) selected by
  unsynthesized polymorphic dispatchers on `valueOf(sa) == 0`
  (`FIFOF_.bsv:111-138` and four more sites), with compiler-side zero-width
  port filtering (`isNotZeroSized`, `AVerilogUtil.hs:1034-1037`) and a
  Bluesim analogue (`zeroSizedType`, `SimPrimitiveModules.hs:72-73`).
- The library hand-rolls what §4 mechanizes: `SPSRAM.bs:73-79` computes its
  Verilog module name as `"RRSPSRAM_" +++ integerToString nwords +++ ...`
  and feeds it to Classic `module verilog` — key mangling by hand, plus a
  `genC` dispatch to a C model (`SPSRAM.bs:45`).
- The monad level exists too: `ModuleContext.bsv` has `Expose`
  (`unburyContext`, line 86-91) and `Hide` (`reburyContext`, line 135-136)
  classes that reify a module context as an interface so a
  `ModuleContext#(c)` module can cross an ordinary `Module` boundary — today
  invoked by hand, because GenWrap's `fixupPolyModType`
  (`GenWrap.hs:581-595`) hard-substitutes the `Module` monad for synthesis.

---

## 2. The proving ground: BVI fallbacks (v1, shipped)

The v1 feature — `fallback <module>;` inside `import "BVI"`, naming a
same-interface pure-BSV module — is both a shipped capability and the
prototype of the contract mechanism. Summary of what it established
(implementation lives on a downstream branch, `verilog-import-fallback`;
none of its symbols — `vFallback`, `BoundaryTarget.hs`, `chkSchedRefinement`,
`wi_boundary_target` — exist upstream yet, verified by tree-wide search):

- **Semantics.** Verilog backend: one shared instantiation wrapped in
  `` `ifdef BSV_SOFT_IP_<vName> `` swapping only the module name; default
  output byte-identical to today. Bluesim: link resolves the instance to the
  fallback's `.ba`, making designs with encrypted vendor IP Bluesim-able.
  Elaborate once: no backend flag read at elaboration; the parent `.ba` stays
  backend-agnostic (`backendMatches Nothing` — `Backend.hs:27-30`). A missing
  fallback is not an error (it means Verilog-only; Bluesim link's existing
  `EBSimForeignImport` fires, `ABinUtil.hs:279-285`); `-require-fallback` is
  opt-in strictness, and a `<top>.fallbacks` sidecar lists swappable
  instances for CI gating.
- **The core mechanism — boundary-targeted synthesis.** Normally synthesis
  *produces* a boundary; here the import's declared `VModInfo` *prescribes*
  the fallback's. The targeting half **forces what can be forced** by
  normalizing the target's clocks/resets/args into the *existing* pragma
  forms (`PPclock_osc`, `PPclock_gate`, `PPreset_port`, `PParg_port`,
  `PParg_param`, `PPalwaysReady`, `PPalwaysEnabled` — `Pragma.hs:115-130`)
  injected into GenWrap's `ppmap`, plus two direct overrides threaded into
  `iExpand` for the names that have no pragma form (method result/RDY/EN and
  method-arg ports, via the `IfcBetterInfo` path). The checking half
  **verifies what cannot be forced**, post-schedule: boundary equality,
  schedule refinement (fallback's inferred conflicts ⊆ import's declared
  `vSched`), and path subset (inferred `vPathInfo` ⊆ declared `vPath`).
- **Representation decisions that carry forward.** The fallback reference is
  a qualified `Id` end-to-end (never a `VName` string — backends must not
  guess names; never ISyntax — it must cross `.bo`/`.ba`). No new pragma
  kind. Validation split by altitude (GenWrap checks interface equality
  where it holds user-level types; TCheck checks argument compatibility
  where it can normalize).
- **What it proved.** (i) Targeting a width-free `VModInfo` is easy and
  polymorphism-agnostic. (ii) Backends need zero changes — everything reads
  `avi_vmi`. (iii) The pragma masquerade *works* but is the disease in
  miniature: the contract had to be translated into configuration because
  pragmas are the only input language the naming machinery understands.
  (iv) The checks caught a real library bug in the OVL pilot (parameter
  width mismatches, since made `SizeOf`-based) — declared-vs-actual
  verification pays for itself immediately.
- **What it deliberately did not cover:** polymorphic imports with computed
  names (SPSRAM/DPSRAM) — the subject of §4 — and fallback expressions with
  free variables, whose closure capture does not cross the `.ba` boundary
  and which are *not reconstructible* from the parent's binary. That wall is
  what forces the key discipline of §4.3.

Two cheap extensions ride on v1 unchanged and are folded into the roadmap:
**fallback-only arguments** (`fallback mkSPSRAM_C(nwords);` — the ifdef swap
emits two separate `VMInst`s sharing wires, so only port connections must
match, not parameter lists; arguments are evaluated at parent elaboration,
recorded on the instance, emitted only in the fallback branch and in
Bluesim), and **cross-package fallbacks** (resolution is already by
qualified Id; v1 scoped these to check-only because naming *forcing* had to
run at the fallback's own compile — under the adapter-injection criterion
of §3.1.1, which drops the forcing requirement entirely, they upgrade to
fully supported: a fallback compiled anywhere, with its natural binding,
qualifies on contract refinement alone).

---

## 3. The boundary contract: one object, two modes

### 3.1 The concept

A **boundary contract** is a first-class compiler object describing
everything a parent may rely on about a synthesized (or imported) module:

```haskell
data Contract = Contract
  { con_name    :: ContractName      -- root name or key-mangled name (§4.4)
  , con_clocks  :: [ClockContract]   -- osc/gate port names, gating discipline
  , con_resets  :: [ResetContract]
  , con_args    :: [ArgContract]     -- port vs parameter, names, clock/reset assoc
  , con_fields  :: [FieldContract]   -- per method: arg ports, result, EN, RDY
                                     --   (incl. inhigh/always-enabled, always-ready)
  , con_sched   :: Maybe SchedContract  -- declared conflict matrix (may be partial)
  , con_paths   :: Maybe PathContract   -- declared combinational paths
  , con_source  :: ContractSource    -- BVI decl | attribute | prior .ba | inferred
  }
```

Two expressivity requirements enter as amendments from the issue sweep:

- **Many-to-one method-to-port mappings (#658).** Real vendor RTL shares an
  argument port between mutually exclusive methods; bsc today ICEs in
  `chkDupWires` because it assumes one wire per method port. `con_fields`
  must support a declared sharing group, made *sound by conditioning on the
  declared schedule* (sharing is legal only among methods the contract
  declares conflicting); downstream checks and the fallback boundary-equality
  comparison key on the sharing declaration, and the parent side generates
  the mux. This also forces a defined answer for what a pure-BSV fallback of
  a shared-port import looks like. (Minimum viable step, independent of the
  contract work: replace the ICE with a positioned error.)
- **Validation at construction (#364, #282).** An incomplete or malformed
  declared schedule today surfaces as an uninformative ICE deep in
  `mkVModuleInfo`, with positions gone; Classic `module verilog` skips the
  synthesizable-interface check the BSV path performs. Contracts are
  validated *when constructed*, where method Ids and positions are in hand,
  identically for both surface syntaxes.

Structurally this is `VModInfo` plus provenance and partiality — deliberately
so. `VModInfo` stays the *output* record the backends read; `Contract` is the
*requirement* record phases consume and verify. The two are connected by one
function with two modes:

- **fill** (infer mode): today's behavior. Elaboration + scheduling produce
  the boundary; the contract is written out (it *becomes* the `VModInfo` and
  its `.ba` record).
- **verify** (target mode): the contract arrives from outside; naming is
  *forced* from it during wrapper generation and elaboration; after
  scheduling, the inferred boundary is checked against it — equality where
  the contract is total (ports), refinement where it is a bound (schedule:
  inferred conflicts ⊆ declared; paths: inferred ⊆ declared).

### 3.1.1 The factoring: IfcContract × BoundaryBinding (A15)

The `Contract` record above — like the `VModInfo` it mirrors — still
conflates two kinds of fact that have different lifetimes and different
consumers, and the factoring should be explicit in the design:

- **`IfcContract`** — the semantic half: method → clock-domain assignment
  (in terms of *formal* domain variables, exactly how `clocked_by` ifc-decl
  pragmas already work), method → reset association, the scheduling matrix,
  and combinational paths stated method-arg → method-result. This half is a
  **type-indexed value**: its well-formedness and meaning are scoped by the
  interface type, so it can travel anywhere the type travels — into a `.bo`
  next to the type declaration, onto an interface *argument* with no module
  behind it, across packages. It is what the parent's scheduler and
  clock-domain checker consume; none of it mentions a wire. Note it is a
  type-indexed *value*, not a constant of the type: `mkPipelineFIFO` and
  `mkBypassFIFO` implement the same `FIFOF#(t)` with opposite enq/deq
  orderings — the type fixes the shape (method set, domain structure), and
  each occurrence (import, module, argument, declared family contract)
  carries its own value of that shape.
- **`BoundaryBinding`** — the mapping from methods to ports, **which can
  vary** at fixed `IfcContract`, and varies per (implementation,
  specialization key), one level finer than the contract: *names* (prefixes,
  renaming, computed per-element names — #142); *multiplicity* (argument
  ports exploded by `SplitPorts`, results split into several output ports —
  #339, several methods sharing one port — #658); *presence* (RDY dropped
  under `always_ready`, EN inhigh under `always_enabled`, zero-width ports
  dropped — presence varies per key: the same module at `Bit#(0)` loses
  ports it has at `Bit#(8)`); *kind* (argument as port vs parameter);
  *declared surface type* (each port's SystemVerilog/b2v type — a
  first-class field of the binding record, not an annotation: it
  participates in rendering (typedef emission, the port declaration), is
  per-key like the rest of the binding (widths, zero-width drops), and is
  what adapters cast between when two bindings type the same wires
  differently — free casts, since packed types are width-equal by the A16
  micro-contract); and *dressing* (opaque pass-through attributes). Under
  §5 the binding is not ad-hoc data but the *output of library rendering
  code* (SplitPorts/WrapField instance choice, naming generic programs);
  the record is the materialized result. With the surface-type field
  populated, the recorded binding *is* the typed port map: b2v-style SV
  emission becomes a rendering of the binding, and waveform/introspection
  tooling (§5.1 consumers 5-6, Appendix B) reads types per port instead of
  re-deriving them by convention.

Today's `VFieldInfo` interleaves the halves per field — `vf_clock`/
`vf_reset` are domain `Id`s while `vf_inputs`/`vf_output` are literal
`VPort`s (`VModInfo.hs:270-286`) — and the compiler already half-practices
the split: clock/reset assignment is declared on the interface type and
*copied* into each module's `VModInfo`, losing the distinction; scheduling
never got the type-side home. The factoring carves along this visible grain.

Three consequences:

1. **The binding is judged against the contract, never the reverse.** Every
   collapse in the mapping needs a license from the semantic half: dropping
   RDY requires `always_ready`; port sharing requires the shared methods to
   be declared conflicting (#658's soundness condition — a scheduling fact
   licensing a port fact); dropping a port requires zero width at this key;
   post-collapse names must be unique (the #307/#424 collisions become
   ordinary checks). This judgment *is* the binding half of fill-or-verify;
   v1's `chkFieldBoundary` (with its always-ready-dropped-RDYs filtering)
   was computing it ad hoc. And it yields the interchangeability criterion:
   **substitution requires only contract refinement (schedule/paths within
   the declared bound) — bindings may vary, and the compiler injects the
   hookup.** The parent never lives at the port level: it holds the
   method-level wire set (`AVInst`, pre-rendering), and instance emission
   *is* the application of a binding to those wires — applying a different
   valid binding to the same wires is the same operation. The licenses are
   what make the adapter derivable rather than heuristic: a presence
   difference adapts because the contract says how (an EN port under an
   always-enabled contract ties to the unconditional will-fire; an extra
   RDY is verified constant-1 and left unread); sharing differences
   collapse the per-method wires each binding's own way; naming is
   aliasing. The one genuine impossibility is a *kind* mismatch in the
   dynamic direction (a dynamic value feeding what the other binding takes
   as a Verilog parameter) — a checkable license failure. Binding-identity
   is the degenerate case where the adapter is empty — v1's choice, made
   for the minimal-output-diff property of the ifdef swap, not because the
   semantics required it (v1's two-`VMInst` mechanism already supports
   per-branch renderings; the default branch stays byte-identical either
   way). Three consequences follow: the *forcing* half of
   boundary-targeted synthesis (the pragma masquerade, the `IfcBetterInfo`
   overrides) stops being load-bearing for fallbacks — a fallback
   synthesizes with its natural binding and only semantic verification
   remains, targeting surviving as an independently useful feature
   (prescribed port names for external flows) rather than a fallback
   prerequisite; cross-package fallbacks upgrade from check-only to full,
   since forcing was the only reason they could not run cross-package; and
   rung-2 dedup canonicalizes *modulo binding*, with instantiation sites
   adapting to the canonical artifact. (Superseded phrasing, kept for the
   record: an earlier draft stated the fallback rule as
   binding-identical + semantically-refining; the binding-identical half
   was v1's mechanism constraint mistaken for semantics.)

   **Refinement (A21), forced by the SplitPorts experience: adapters are
   arbitrary functions, not wire glue.** `toWrapField`/`fromWrapField` and
   `SplitPorts` instances are deliberately user-implementable, so a
   rendering can re-encode arbitrarily; two lawful bindings of one
   `IfcContract` are related only *through the semantic interface value*,
   and the adapter from A-rendered wires to B-rendered ports is the
   elaboration of `toB ∘ fromA` — a function composition, injected and
   typechecked like `wrapModule` and elaborated by the same evaluator, not
   a compiler wire-mangling algorithm. Consequences: (i) wire-only adapters
   are the *compression*, not the mechanism — for derived-`Bits`/structural
   instances the composition constant-folds to extract/concat, but the
   general case is real combinational logic on boundary paths (the boolean
   arg→result path relation composes, so contract path verification
   survives; physical delay is outside bsc's model). (ii) The data/control
   split: function composition covers the data plane; RDY/EN/clock/reset
   adaptation is protocol, stays structural, and is governed by the
   licenses above — arbitrary functions do not belong on will-fire paths.
   Data-plane correctness is the round-trip law (`from ∘ to = id` on the
   semantic value) — the WrapField laws replace per-axis license
   enumeration there. (iii) `BoundaryBinding` must record the *rendering
   dictionary tree*, not just the port relation: composing `fromA`
   cross-artifact requires A's conversion functions, resolvable precisely
   because dictionaries are nameable, hashable, resolved-before-elaboration
   values (§4.3's slogan, paying out again). (iv) mkOneOf's static list
   (§3.6) becomes load-bearing for a new reason: arbitrary-function
   adapters must be *elaborated*, and elaboration belongs at parent
   compile — possible exactly because all N candidates are enumerated
   there, with link merely selecting. Open-world, link-time-discovered
   substitution requires either binding-compatible artifacts or a re-render
   step at link — a stated restriction, not a discovered one.

   **A24 — per-field rendering witnesses: two functions, one reference,
   never bodies.** The representation consequence: each `BoundaryBinding`
   field entry gains `render :: Maybe WitnessRef` — a qualified reference
   (name + hash) to the rendering instance dictionary, *not* stored code.
   The wrap/unwrap pair (`toWrapField`/`fromWrapField`,
   `Prelude.bs:4622/4626`) are the two methods of that one dictionary, so
   a single reference denotes both directions — and the pairing-by-class
   makes the A21 round-trip law a per-instance obligation rather than
   cross-artifact coordination (an adapter uses A's `from` and B's `to`,
   each coherent with its own partner). Both directions are needed even
   though any artifact *bakes in* only one (the module's netlist elaborates
   `to`; each parent elaborates `from`; adapters need the unused
   direction — a decisive reason references beat residual bodies, which
   capture only the used one). Bodies never enter `.ba`s: that would
   re-open the closure-capture wall (§2), couple artifacts to ISyntax
   versions, and defeat name-based hashing. The evaluator rehydrates the
   reference against `alldefs` at adapter elaboration (parent compile, per
   the static list). `Nothing` = the canonical structural (pack-based)
   rendering — which is exactly what a hand-written BVI import's binding
   already implicitly is, so the entire existing artifact corpus is
   well-formed under the new field, and adaptation to witness-less
   bindings is possible precisely in the structural cases. Third
   occurrence of the design's central serialization move: *store the name
   of the function pair, and arrange that names suffice.*
2. **A1 (§3.5) becomes representable.** An interface argument has no VName
   and no ports; a contract trapped inside `VModInfo` cannot attach to it.
   The factoring is A1's structural prerequisite. Likewise family contracts
   (§4.3) are `IfcContract` values declared at the polymorphic type and
   verified per key, and declared schedules (§3.3) can be stated once on the
   *interface* and inherited by every implementation.
3. **Record the mapping, not just its output.** The `.v` is today the only
   witness of methods → ports and it is lossy both ways; tooling that needs
   the inverse (waveform decoding, `expandPorts`-style reconstruction,
   bluetcl display — §5.1 consumer 5) re-derives it by string convention.
   `BoundaryBinding` in the `.ba` stores the actual relation (method/arg →
   port set, with the license for each collapse); the wrapper generator has
   it in hand at fill time anyway.

Altitude summary: `IfcContract` — type-indexed value, `.bo`, scoped by the
type; `BoundaryBinding` — per (implementation, key), `.ba`, produced by
library rendering code, validated against the contract; `VModInfo` — their
**materialized join** per instance, so `avi_vmi` and everything downstream
stay byte-for-byte as they are (the §1.2 invariant is untouched).

Everything in this document is an instance of one of the two modes:

| Feature | Contract source | Mode |
|---|---|---|
| Ordinary `(* synthesize *)` | inferred | fill |
| `import "BVI"` | BVI declaration | (no body — contract only) |
| BVI fallback (§2) | the import's declaration | verify, on the fallback body |
| Declared schedule attribute (§3.3) | source attribute | verify (schedule part) |
| Schedule regression pinning (§3.4) | previous `.ba` | verify (schedule part) |
| Polymorphic specialization (§4) | per-key: inferred; optional family contract | fill per key; verify family claims |
| Interface-argument contracts (§3.5) | attribute on the argument's ifc type | verify at the use site |

### 3.2 Where it lives in the pipeline

The contract object is introduced *between* the current phases, subsuming the
fallback branch's `wi_boundary_target` (its prototype):

1. **Pre-typecheck:** only *marking* — which defs are boundaries, and where
   their contracts come from. No type computation, no flattening, no minting.
2. **Post-typecheck:** flattening and wrapper generation on **normalized**
   types (§5). Type-function-computed interfaces work by construction,
   because the typechecker has already run. Mid-flow `runTI` is proven by
   `AAddSchedAssumps.hs:225`.
3. **Elaboration:** naming consults the contract *directly* — no pragma
   round-trip, no `IfcBetterInfo` reconstruction. (`IfcBetterInfo.hs`, which
   says of itself "this package needs re-thinking", is deleted, not
   re-thought.)
4. **Post-schedule:** the one fill-or-verify function. Today's `deffun`
   continuation and the fallback branch's `chkBoundaryTarget` are the two
   halves of this function, currently living in different countries.

### 3.3 Cheapest valuable extraction: the declared-schedule attribute

Before any of the larger work, one piece of v1 generalizes immediately: allow
any synthesized module to declare its intended schedule —

```bsv
(* synthesize,
   schedule "enq" CF "deq",
   schedule "enq" C  "clear" *)
module mkMyFifo (FIFOF#(t));
```

— verified post-schedule by the same refinement check the fallback uses
(inferred conflicts must be ⊆ declared; a declared-CF pair that the scheduler
finds conflicting is an error naming the method pair). This requires **no new
machinery** beyond porting `chkSchedRefinement`: the scheduler already trusts
declared `VSchedInfo` for imports (`ASchedule.hs:1710-1712`), and
`always_ready` shows the declare-then-prove pattern end to end
(`AAddScheduleDefs.hs:190-197`). It converts the promise every BVI import
already makes *on faith* into something a BSV module can make *checked* — and
the sweep shows a steady cluster of demand for declared, checked scheduling
(§8.4: #194, #316, #547, #540).
Had the library carried the documented schedule of `mkDRegA/U` as a declared
contract, the divergence reported in #547 (documented SBR, actual C) would
have been a compile-time error at the library's own build.

Under the A15 factoring the primary declaration surface moves up a level:
a declared schedule is an `IfcContract` value that can be stated once on
the *interface* (or as a named contract value) and verified by every
implementation — one declaration covers every `mkFIFOF`, fixing
#547-class documentation drift where the documentation actually lives.
Per-module declarations remain as refinements.

Three refinements from the sweep:

- **Verification must see through inlineable primitives (#631) — amendment.**
  A method whose RDY routes through `mkWire` is truly always-ready after wire
  inlining, but today's `always_ready` proof runs while submodules are black
  boxes and rejects it. The contract's verify mode must include
  inlineable-primitive (RWire/CReg) output definitions in its proof context —
  or stage verification after wire inlining. Otherwise declared schedules and
  family-uniformity contracts will reject legal wire-routed implementations,
  a common idiom, and kill adoption of verify mode.
- **One demotion policy (#230).** `always_ready` failure has a bespoke
  `-unsafe-always-ready` flag today; contract-verification failures (G0006
  and the new refinement-check family) should share one uniform
  demotion/strictness mechanism.
- **Partial declarations are required, and error quality is the bar (#540).**
  Declaring only the pairs you care about must be legal, and a verify-mode
  failure must name the method pair and both relations —
  `no_implicit_conditions` shows how a verified micro-contract with a vague
  error message frustrates rather than helps.

`enabled_when_ready` (#607) is a third micro-contract of exactly this kind
and gets its principled home in the same mechanism, as does the phase-smear
class where a pragma is honored by one check and not another (#657:
`chkDupWires` counts a RDY port that `always_ready` has elsewhere dropped —
v1's boundary comparison already implements the always-ready-filtered
discipline that check lacks).

### 3.4 Schedule regression pinning

Because a contract can be sourced from a previous `.ba` (`con_source = prior
.ba`), a build can pin a module's boundary: "this refactor must not change
`mkCore`'s schedule." The compiler re-verifies the fresh inferred boundary
against the recorded one and reports drift as a structured diff (method pair,
old relation, new relation). This is a pure consumer of the verify mode; no
language surface is needed beyond a flag (`-pin-boundary <ba-file>`). Under
the v0 plan (§3.6), the `contractOf` primitive sourced from a prior `.ba`
*is* this feature — pinning comes nearly free with the extraction
primitive.

### 3.5 Contracts on interface *values*, including interface arguments

Amendment recorded from the long-horizon projects doc: interface arguments to
synthesized modules were dropped historically because the compiler could not
capture their scheduling. Under declared schedules the situation inverts: a
*used* interface (argument) carrying a declared conflict contract is the dual
of a *provided* interface carrying one, and `ASchedule`'s existing trust of
declared `vSched` for imports is the primitive for both directions. The
parent verifies what it provides to the argument; the module trusts what the
contract declares. This is the research-shaped end of the contract work
(delivery-model: after the module-boundary contracts are solid), but the data
model above already accommodates it — `con_fields`/`con_sched` attach to an
interface value, not to a module per se.

The use-side dual is already a reported hole: #545 observes that bsc does not
enforce correct *use* of `always_enabled` methods (calling one from a
conditioned rule is silently accepted). Both-direction verification of
interface-value contracts is the missing check, named.

### 3.6 The combinator endgame: mkOneOf (A19)

The convergence point of §3 and §5, stated as a type:

```
mkOneOf :: IfcContract -> [(String, Impl a)] -> Module a
```

One declared contract, N named implementations, one module. Each piece of
the signature cashes in a different part of the design:

- **`IfcContract` as an ordinary value argument** is the A15 factoring's
  payoff: a contract you can pass to a function must be a first-class,
  type-indexed value scoped by `a` — constructible from source attributes,
  a BVI declaration, a prior `.ba`, or a library constant. The attribute
  surfaces of §3.3 demote to sugar over constructing this value.
- **`[(String, Impl a)]` is the N-ary fallback.** v1 was one contract, two
  bodies, the second special-cased into `vFallback :: Maybe Id`; here it is
  one contract, N named bodies (vendor IP, soft BSV, sim-optimized...). The
  `String`s are the selection keys: per-name macros generalize
  `BSV_SOFT_IP_<vName>` (and solve the macro-namespacing question v1 dodged
  by keying on the import's name), the `.fallbacks` sidecar generalizes to
  a selection manifest, Bluesim link selects by name. The list is a
  *literal*: the variant set is statically enumerable at the module's own
  compile, staying on the right side of the artifact-ownership wall (§4.5)
  exactly as the derived `_z*` variants do. An `import "BVI"` is an `Impl`
  with no elaborable body — contract + binding only.
- **A17 is the enabling move.** Forcing two bodies to binding-identity was
  v1's ugliest machinery; forcing N would be unworkable. Under adapter
  injection each `Impl` synthesizes with its natural binding, is verified
  against the shared contract, and the compiler closes each loop at the
  instantiation. mkOneOf without A17 is a pain multiplier; with it, a fold.
- **The parent schedules against the declared contract, not any impl** —
  v1's semantics, load-bearing at N: impls may have genuinely different
  inferred schedules, all refining the declaration, and the parent must
  consume only the declaration or flipping a selection macro would change
  parent scheduling. Elaborate-once survives: all N bodies produce
  artifacts, selection is late-bound (netlist ifdef/generate; Bluesim
  link), the parent `.ba` stays backend-agnostic.
- **`Impl a` is an existential package (A23):** `∃ w. (WrapIfc a w
  evidence, Module w)` — an implementation bundled with *its own* rendering
  evidence. The domain/codomain of the conversion functions is not a
  value-level list of ports but the **wrapped interface type `w`**: the
  solver-computed flattened counterpart of `a` (`WrapIfc a w | a -> w`), a
  type-indexed product whose *leaves* are name-tagged bit-vector positions
  and whose *skeleton* is the protocol structure (Action/ActionValue, EN,
  typed ready) — "a list of ports" is `w`'s erasure, not its type. A
  value-level list cannot serve: leaves are heterogeneous, the functions
  must typecheck once in the Prelude (port structure = a type function of
  `a`), and elaboration needs distinct leaves to become distinct wires.
  Ports exist only after the boundary assembler consumes `w`; the to/from
  functions are ordinary ISyntax-typed functions `a -> w` / `w -> a` and
  never see a port. This grounds A21's data/control split (conversions are
  arbitrary on leaves; the spine belongs to the assembler and the
  licenses), makes `BoundaryBinding` the *value-level shadow of `w`*
  (entries 1:1 with leaves — not independent data to keep consistent, the
  reflection of the type the wrapper computed), and makes the recorded
  rendering-dictionary tree the *serialized existential witness* enabling
  cross-artifact adaptation. The parent is parametric in each impl's `w`;
  the only shared type is `a` — the formalization of "bindings can vary."
  `stubOf` manufactures the whole package from the contract: a default
  `w`, trivial evidence, a generated `Module w` body.
  **The ∃ is specification vocabulary, not a type-system requirement** —
  no higher-rank types are needed; bsc's rank-1 + MPTC/fundep system
  suffices, three ways: the quantifier is *staged away* (elaboration is the
  meta-level; each impl's `w` is concrete at its own elaboration, and
  mkOneOf, like `wrapModule`, is Prelude-typed but evaluator-meant);
  *pre-application* erases `w` at the seam (the surface list is
  `[(String, Module a)]` with each element's rendering already discharged
  inside, and the witness lives as *data* — the serialized dictionary tree
  in the `.ba` — not as a type); and the library already ships the rank-1
  idiom for rendering variance (`ShallowSplit`/`DeepSplit`/`NoSplit`
  newtype tags, `SplitPorts.bs:9-13` — variance moves into the tag, the
  fundep stays functional). The type-system bill is exactly what bsc has;
  the real expressiveness risk remains the #901-class instance/solver
  limits, which constrain how the generic programs are written, not
  quantifier rank.
- **`wrapModule` (§5.3) is the unary case** — `mkOneOf c [("only", impl)]`
  modulo the name — so ordinary synthesis, BVI-with-fallback, and N-way
  soft-IP selection are one function at three list lengths. What stays
  primitive underneath is what was always primitive: reentrant per-impl
  synthesis (§4.4) and the fill-or-verify hook; mkOneOf is typechecked in
  the Prelude but *meant* by evaluator machinery, like `wrapModule`.

mkOneOf is the first combinator of a **boundary algebra** — contracts as
values, `Impl` as bodies-awaiting-boundaries, combinators over both. Its
successors are already in this document in feature clothing: pinning
(contract sourced from a prior `.ba`, §3.4), targeting (a prescribed
`BoundaryBinding` for external flows — an optional wrapper now, not core
machinery), the interface-argument dual (§3.5), and composition (mkOneOf
under mkOneOf, selection-key spaces multiplying). The compiler's three jobs
(§5.5) are unchanged; the user assembles them.

**First uses: `import "BVI"` fallback, and stubbable modules.** The
fallback is mkOneOf's shipped two-body case. The second first-use is the
first *derived* `Impl` — the point where the contract turns generative:

```
stubOf :: IfcContract -> Impl a
```

A stub is computable from the contract alone (outputs tied off — X in
Verilog, defined-zero in Bluesim, optionally `$display`-on-call; RDYs per
the declaration; ENs accepted and ignored; maximally-CF schedule), and
satisfies every check by construction: all-CF refines any declaration,
swap-safety is structural because the parent schedules against the declared
contract, and drift — the classic failure mode of hand-maintained stub
files — is impossible, since the stub regenerates from the same value the
real implementation verifies against. Per-key stubs are free (the contract
is width-free; widths come from the key). The two uses compose: `stubOf`
is the default fallback everyone gets without writing anything — today an
un-fallbacked vendor import means `EBSimForeignImport` and an
un-Bluesim-able design; with `fallback stub;` (or auto-derivation under a
flag) every BVI design becomes Bluesim-able immediately, with the real soft
model as the upgrade path rather than the entry fee. Pointed at synthesized
modules, the same mechanism makes every `(* synthesize *)` module
stubbable — `mkOneOf contract [("real", impl), ("stub", stubOf contract)]`
with the second entry implicit under a pragma — giving subtree stubbing
(fast sim, DV mocking, synthesis blackboxing, bring-up) selected at
simulator compile time with no re-elaboration.

**The governing principle (A20): design for type and schedule/clocking
compatibility, never for wire compatibility — port names stop being API.**
Wire compatibility is something the compiler *provides* where needed, never
something the design *requires* — the same inversion typed languages made
when the compiler took ownership of the calling convention. Today Bluespec
hand-manages its calling convention (renaming pragmas, `RDY_` conventions,
`expandPorts.tcl`, integration by port-name string-matching). Under the
principle: the boundary ABI is semantic — `(interface type, IfcContract)`
is a boundary's identity, and anything refining it substitutes, however it
renders (mkOneOf's list is heterogeneous *because* entries never agree on
wires); binding changes stop being breaking changes (a library adopting
better `SplitPorts` instances, A16 surface types, or #339 result splitting
breaks no parent — rendering was never API, decoupling port-shape evolution
from API stability); identity, caching, and rung-2 dedup key on semantics,
with `VModInfo` (the join) a per-rendering artifact; and wire coupling
survives only at *declared edges* — testbenches poking ports by name,
external synthesis flows, pinout contracts — where a `BoundaryBinding` is
frozen deliberately, the way an FFI pins a calling convention. In one line:
**wire compatibility is never required internally, only provided
deliberately at edges.** The duty it imposes: the adapter generator must be
total over licensed bindings — every §3.1.1 variation axis either adapts or
fails with a named license violation, never silently — and glue lives
inside the selected branch (aliases and tie-offs are wires; the shared-port
collapse is the mux the binding already implied), so unselected variants
compile out and the winner pays only its own rendering.

**mkOneOf v0 — the shortest path (A25).** Two features plus an escape
hatch, deliverable on top of the v1 branch with its machinery reused
wholesale (targeting, refinement checks, two-`VMInst` ifdef emission,
link-by-Id resolution, format-bump discipline, sidecar). One
selection-group mechanism; two contract sources; three entry kinds.
Adapters, the full contract object, and first-class `Impl` values are
explicitly deferred — v0 forces bindings with v1 targeting, no adapter
half-measures.

*The concrete driving pair (minimum cut):* (1) **BVI fallbacks** = v1
as-is, zero additional work at N=1. (2) **Stub-group selection for tile
grids** (entries = several stub implementations — null, loopback,
traffic-gen — of a real module, selected per grid position) via an
**evaluator primitive, not an attribute**:

```
mkOneOf_ :: [(String, Module a)] -> Module a   -- first entry = primary/contract
```

Contract extraction is a `conAp'` pattern-match, not a source-surface
feature: parents see every separately-synthesized module — BVI or BSV —
uniformly as `ICVerilog { vInfo, isUserImport }` (`ISyntax.hs:774-777`;
`isUserImport=False` for synthesized BSV), instantiated ones as
`ICStateVar` with the same `VModInfo`. The primitive peeks each entry's
con to extract its boundary *without instantiating it* (one careful case:
intercept before `newState`), runs v1's boundary-equality/refinement
checks on the extracted contracts in the evaluator (CF-everything stubs
pass refinement trivially; the boundary check keeps hand stubs from
drifting), and instantiates exactly one shared state var — the primary's
`VModInfo` with the alternates list attached — feeding v1's `VMIfDef`
emission and link resolution generalized 2→N. This beats the attribute
route on every axis: no parser/pragma work; **per-instance selection
falls out free** (the primitive runs per call site, each already a
distinct named instance, so per-position macros
`BSV_IMPL_<parent>_<inst>_<name>` are just how the instance emits —
stubbing `tile_3_7` while `tile_0_0` stays real is default behavior, not
mechanism); **type-indexing free** (all entries `Module a` — "a contract
is always a contract for a particular type" enforced by ordinary rank-1
typing before the evaluator compares boundaries); and it *is* embryonic
mkOneOf (contract implicit as first entry now; explicit `Contract a` via
the extraction primitive as the upgrade). Naming note: the trailing
underscore follows the library's internal-form convention (`FIFOF_`,
`mkFIFOF1_`) — a `0` suffix would wrongly read as a zero-width variant
per the `FIFO0`/`RWire0` convention. Bluesim: path-keyed selection
(`-use-impl <path>=<name>`) resolves `.ba`s *before* C++ generation, so
stubbed positions never generate or compile the real module's C++ — link
cost scales with what is real (directly attacks matx#14662/#10837).
**Revision (final v0 shape): the specified contract comes first.** The
implicit first-entry form was the one variant that does not generalize —
and it is inference-as-spec: the group's contract silently becomes
"whatever the primary does this week," the #547 disease at group level
(stubs verified against a drifting implicit contract flip on unrelated
primary edits). Specified-first is declare-then-verify — the design's
north star — with the *real* implementation verified against the
declaration too, no longer privileged; it un-conflates the primary's
three roles (contract source / default branch / binding source, each now
explicit); and it cuts the rebuild cascade (parents schedule against the
declaration, so primary-internal schedule changes within the bound stop
perturbing parents). Cost stays inside the primitive route because
contract literals are *library values*, validated at elaboration — no
parser work:

```
mkContract :: [SchedDecl] -> IfcContract a   -- names checked against a at elaboration
sched      :: String -> SchedRel -> String -> SchedDecl
contractOf :: a -> IfcContract a             -- bootstrap/extraction aid (boundary-rooted)
mkOneOf    :: IfcContract a -> [(String, Module a)] -> Module a
```

Ergonomics that make hand-written contracts viable for a large tile
interface: **partial declarations with a conservative default**
(unspecified pairs = conflict — safe in the refinement direction;
declaring more only grants more freedom) and the **extract-then-freeze
workflow** (`contractOf` + a dump flag prints the primary's current
matrix as a pasteable literal — bootstrap from reality once, then drift
is a compile error). `contractOf` attaches to the interface *value* (A15
in the surface language; type-indexing inherent; uniform over provenance,
eventually including interface arguments — the first surface for
A1/§3.5); non-boundary-rooted values are a positioned elaboration error.
It also independently serves DV-side contract checks and later
`.ba`-sourced pinning.

*The front-end simplification (A26): `import "BVI"` and Classic
`module verilog`'s successors parse directly into contracts.* The BVI body
grammar is already a contract-literal sublanguage; parsing it into
`(IfcContract a, BoundaryBinding)` values makes `import "BVI"`, Classic,
and `mkContract` three notations for one semantic constructor — "BVI
import = contract with no body" become literal, conceptually
`importVerilog :: VName -> IfcContract a -> Binding a -> Module a`, an
`Impl` with no body. Consequences: #620 (BH/BSV parity), #282 (Classic
skips checks), and #364 (ICE at `mkVModuleInfo`) close *by construction* —
validation happens once at contract construction, positions in hand,
whatever the surface; import-with-fallbacks stops being special syntax
and becomes ordinary composition (an external entry in a mkOneOf group;
v1's `fallback` clause = list syntax); the A20 line becomes structural
(the import surface legitimately declares wire names — it *is* the frozen
edge — while `mkContract` never does); and, sneaky-big, **validation
moves to elaboration, which is post-typecheck by construction** — the
contract route bypasses `CVParser` pre-flattening and GenWrap's
`fixCModuleVerilog` (one of the four flattening duplicates), obtaining a
slice of W5/W7's benefit for imports without moving GenWrap, and putting
the import path forever out of reach of the type-function-blindness
class.

*The implementation floor (A27): the import primitive is smaller than
v1.* Below the A26 parse, a Verilog import reduces to one evaluator
primitive:

```
primImportVerilog :: String -> IfcContract a -> BoundaryBinding a -> Module a
```

— a `conAp'` case that validates contract∪binding against `a`'s Rep
(positioned, post-typecheck by construction), performs the A15 **join at
construction** into a `VModInfo`, and emits
`ICVerilog { isUserImport = True, vInfo, vMethTs from a }` — which
`handlePrim`/`newState` consume unchanged (`avi_vmi` invariant untouched;
the primitive is the single place the join lives when formats later
split). This replaces the entire old import path (`CVParser`
pre-flattening → CSyntax forms → `fixCModuleVerilog` → `mkVModuleInfo` →
IConv), through which v1 had to thread the fallback across altitude
splits; on the new path fallbacks are mkOneOf composition a layer above.
Because the arguments are ordinary evaluator values, two projects arrive
as consequences: **computed module names** (the `String` is computed —
the SPSRAM idiom becomes ordinary code; #679's one-body-many-modules
want is a function application) and **computed contracts/bindings**
(import-family functions for vendor IP generators — the kernel of the
"redo Verilog imports around SplitPorts" project). Migration by
coexistence: old syntax keeps the old path; the successor feeds the
primitive; `fixCModuleVerilog` dies with its last producer.

*And stubbing comes free (completing the kernel).* With the primitives in
place, stubbing is a composition, not a feature: `genericStub` — a
trivial interface built generically over the existing `Generic`/`Rep`
machinery (value methods `unpack(0)`, Actions `noAction`; the same
program shape `SplitPorts` already demonstrates) — is **pure library
code, zero compiler delta**; `mkOneOf contract [("real", mkTile),
("stub0", mkTileStub), ...]` verifies it against the contract (trivially
passing), and `contractOf`/extract-then-freeze supplied the contract
without hand-writing it. The earlier "derived `stubOf`" item leaves the
deferred-compiler-work list — it was never compiler work. One-line
caveat: v0 needs the three-line `(* synthesize *)` wrapper per interface
(a polymorphic module cannot carry the pragma — the #543 wall), the
residue W8's specialization-first synthesis deletes. Kernel accounting:
`mkContract` validation, `contractOf`, `primImportVerilog` = one `conAp'`
case each; `mkOneOf` + N-ary `VMIfDef`/link = the ~2-week core;
`genericStub` = zero. Every driving feature — BVI fallbacks, per-instance
tile-grid stub selection, external anchors, computed imports, drift-proof
stubs — is a composition of those five.

*v0 binding semantics: exact match on the port-connection surface.*
`BoundaryBinding` in v0 is today's wire-level `VModInfo` port structure,
and group entries must match exactly — port names, arg kind (port vs
parameter), presence (dropped RDY/EN status), port properties,
clock/reset port names — with one inherited exemption: **parameter lists
need not match** (branches are separate `VMInst`s sharing wires only —
the v1 seam that enabled fallback-only arguments). Three regimes satisfy
it: **canonical-by-default** (bindings derive deterministically from the
interface type + pragmas, so plain same-ifc `(* synthesize *)` modules
match automatically — the tile-stubbing case costs nothing); **v1
forcing** (import-rooted groups: the vendor binding wins, BSV entries are
targeted to it via the declared-fallback route); **manual pragmas** (the
escape hatch). Mismatch = a positioned error showing the binding diff
(port, entry, expected vs actual — both records in hand). And the
constraint is **permanent, not provisional**: the core construct stays
exact-match forever, and A17/A21/A28 arrive as a *marshalling layer on
top* — `adapt :: IfcContract a -> Impl a -> Impl a`, a generated wrapper
module whose outer binding is the group's exactly and whose body is the
elaborated `⟦A⟧.from ∘ ⟦B⟧.to`. The core never grows modes; adapters get
a normal artifact story (the wrapper is an ordinary module, inside the
selected branch because it *is* the branch's module — the A21(iv)
link-time restriction evaporates); verification composes with no new
rules (marshalled entries check like any entry; marshalling correctness
is the A28 round-trip lemma); and A20 gets its operational reading —
wire compatibility *required* by the core, *provided* by the layer. Cost:
one hierarchy level per adapted entry.

*The brutally stripped kernel (definitive v0 primitive set):*

```
IfcContract a, BoundaryBinding a      -- abstract types; NO literal syntax in v0
primImportVerilog :: String -> IfcContract a -> BoundaryBinding a -> Module a
                                      -- (halves from existing BVI syntax internally)
contractOf :: a -> IfcContract a      -- ICStateVar root       (un-join,
boundaryOf :: a -> BoundaryBinding a  --                        two halves)
mkOneOf_ :: IfcContract a -> [(String, ModuleRef)] -> Module a
         -- ModuleRef = qualified Id; binding derived (canonical) in v0
```

*Extraction-only revision (final): no contract literals in v0 at all.*
Contracts come from two sources only: the existing BVI import syntax
(feature 1 — already parsed by v1 machinery) and extraction (feature 2 —
`contractOf`, or extract-from-reference-entry for groups). This deletes
the estimate's largest and riskiest item — the literal grammar, the
`pMethodVeriProt` factoring, *and* the two CSyntax constructors with
their 16-file `CExpr` fan-out and `GenBin` cases (extraction mints its
`ICon` directly in the evaluator; no CSyntax surface exists). What it
costs: no spec-first authoring, no partial declarations (extracted
contracts are total), and feature 2's contract source is the reference
entry — inference-as-spec, answered by **golden pinning**: the compiler
records the group's resolved contract as a sidecar artifact; the printer
renders it human-readable (checked in, diffed in review); rebuilds verify
against the pin. Two sub-commitments keep this sound: verification is
**refinement-directional** (less-conflicting-than-pin passes;
more-conflicting fails — benign improvements don't churn goldens), and
**the printer output is the future literal grammar** (A26 remains the
destination; today's goldens become tomorrow's source literals verbatim).
Declare-then-verify survives operationally: "declare" = freeze a reviewed
extraction. **Estimate under extraction-only: ≈20-30 engineer-days,
point ≈24 (~5 expert-weeks) — under one v1-unit.**

*The peek, revisited soundly: an alternate module-monad handler.* The
`Module a` peek was killed for *sandbox* evaluation (heap references
don't port to a separate evaluation); it returns soundly as a **peek
mode in the same evaluation**: module-monad sequencing evaluates
normally, benign pre-boundary effects (names, `primSavePortType`,
clock-context reads) are no-ops under the mode, and
`newState`-on-`ICVerilog` is *intercepted* — capture the `vInfo`, escape
(capture-and-abort, not a full no-op interpretation). Same heap, so no
portability problem: cells allocated during the peek are abandoned dead,
not dangling; effects are gated by mode, not rolled back. The first
foreign bind is the right one because a synthesized module's cross-`.bo`
form *is* wrapper-around-its-own-`ICVerilog`; the guard against
non-synthesized entries (whose first inner instantiation would
masquerade) is matching the captured boundary against `a`'s
symtab-flattened view — validation the kernel needs anyway. Buys back
`contractOfM`/`boundaryOfM` and, decisively, **`Module a` entries with
applied arguments** (`mkTileStub(cfg)` — parameterized alternates,
inexpressible as bare Ids). Cost ~+3-5d over the Id route (mode flag,
interception, escape/unwind plumbing — the delicate part — and the
guard); the Id route remains the v0 floor, with the handler-peek as the
documented upgrade, promoted only if per-position stub configuration is
a day-one need. Architectural rhyme: a swappable module-monad
interpretation is §5.5's monad-indexed boundaries in miniature — the
peek handler is the first instance of "the module monad's meaning is a
parameter."

*Final v0 shape: the kernel is read-only over boundaries.* Without
literals, `primImportVerilog` has no input source while imports continue
down the old path — two representations that never compose ("BVI
contracts aren't clean"). Resolution: the primitive leaves v0 too.
Imports stay wholly on the old path and participate through their
*recorded* `VModInfo`, un-joined on demand (`ICVerilog` carries `vInfo`
whichever path built it — import as group root/entry via Id resolution,
as `contractOf` source via `ICStateVar`, zero new machinery). v0 = four
read-side pieces: the abstract types; `contractOf`/`boundaryOf` (the
un-join); `mkOneOf_` (Id entries: resolve → compare → select); printer +
golden pinning. The write side — literals, `primImportVerilog`'s join,
validation-at-construction (#364/#282), computed imports, A26's
parse-into-contracts — is one coherent round-2 package (the literals
feed the primitive; the primitive gives the parse its target;
`fixCModuleVerilog` dies only when both arrive). Read-before-write is
the right risk ordering: the read side serves both driving features and
never changes how anything compiles today. **Estimate: ≈18-26
engineer-days, point ≈21-22 (~4.5 expert-weeks).**

*The WrapInterface substitute (A34): adoption instead of derivation.*
`WrapInterface` — generating the type→wire mapping and back, over the
full carrier (interfaces, clock/reset members, Verilog parameters) — is
the *proper* derivation of a synthesized module's wire mapping, and v0
doesn't have it. The substitute: **don't derive, adopt.** The existing
pipeline (GenWrap spine + #729 leaves) already computes the full mapping
for every synthesized module and records it (`VModInfo` in
`.ba`/`ICVerilog`, covering methods, clocks, resets, parameters); the
kernel *reads recordings* — the group adopts the root's recorded
binding, entry checks compare recordings, `contractOfM` is the recording
made WHNF-reachable. Sounder than re-derivation: the recording is the
mapping the netlist actually has, produced by the real machinery under
the real pragmas at the module's own compile. Honest gap — only
`WrapInterface` can map something *never synthesized* (contract-only
interfaces for round-2 `primImportVerilog`, new keys for W8, targeting
for external flows); none are v0 features. Bridge for the fresh case if
it arrives early: **derive by synthesizing a witness** — generate a
trivial module (the stub) at the interface and harvest *its* recording;
the pipeline as a derivation subroutine at artifact granularity,
observer-clean, automatable (a hidden witness module for a contract-only
ifc), and self-obsoleting (`WrapInterface`'s output must equal the
witness's recording — a free oracle test, same pattern as
annotation ≡ fork). Stated precisely: **GenWrap remains the sole
wire-mapping producer in v0 — the kernel doesn't replace it, it
*quarantines* it.** GenWrap runs at each definition's own compile (the
`(* synthesize *)` pragma is exactly the marker "a mapping was derived
and recorded here" — which is *why* entries must be synthesized), never
at the group site, never on demand; every kernel interface to the
mapping (un-join, adoption, annotation, comparison) is
**producer-agnostic** — it consumes recordings, not the machinery that
made them. That is what makes the eventual swap silent: when
`WrapInterface` replaces GenWrap as producer, every v0 consumer keeps
working unmodified, having never known who produced the recording.

*Correction (the recording is the residue, not the morphism).* GenWrap's
recording is not the clean A32 mapping: the field→port correspondence is
keyed by flattened string names (`mkUSId` convention), not carrier field
identities; port *types* live in a side table (the `primSavePortType`
data), not in the mapping; conversion witnesses (how values move through
pack/unpack — decisive under custom `Bits`) are unrecorded; licenses are
inferable from port properties at best. Three-part resolution: (1) **v0
never needs the clean morphism** — exact-match and refinement are
recording-vs-recording, closed within the convention; the one
type-touching seam crosses via the symtab's flattened `FieldInfo` view,
the compiler's *own* convention table — convention-internal end to end.
(2) **The "other stuff" is misfiled treasure**: the port-type table is
A16's surface-type ancestor, port properties are proto-licenses — the
un-join's real job is *sorting* (`VModInfo` + port-type table) by A32
role, with documented partiality (witnesses absent, licenses inferred).
(3) **The producer-agnostic claim has a named expiry**: fully true only
when the recording *format* is re-founded in A32 shape (morphism keyed
by field paths and member kinds, types inline, A24 witnesses and
licenses recorded) — scheduled for when `WrapInterface` lands, producer
swap and format upgrade together, old recordings readable as the
degenerate case.

*A35 — the alternative formulation: declared-binding synthesis.* Binding
*declared and applied*; clocking, scheduling, **and paths** all
*derived* — the dual of `import "BVI"` (binding+contract declared, no
body) and the fill-mode complement of v1's targeting. The slogan, mapping
exactly onto A32: **carriers from the type, morphism declared, relations
derived** — everything relational (field-level sched/clocking,
port-level paths) is computed by the machinery that owns it; only the
field→port mapping is authored, and only where it deviates. The syntax basically exists (the BVI body's
port/enable/ready clauses) and the application mechanism is proven (v1's
declared→pragmas+overrides path — the pragma masquerade becomes the
*implementation* of a clean surface rather than the surface). What it
buys: (1) **it solves the A34 residue at the producer** — the morphism
becomes a parse product keyed by real field names (no `mkUSId`
convention, no side tables); the recording stores the declared mapping
verbatim plus the derived halves (clocking confirmed by elaboration,
sched/paths by analysis) — *mechanism old, data clean*, retiring A34's
format-re-founding expiry (the clean format arrives at declaration time,
producer unchanged); (2) **groups get exact-match by construction** —
one declared mapping applied to every entry's synthesis, each entry's
contract derived and checked, v1's forcing through a clean surface;
(3) **targeting gets its legitimate surface** (frozen edges: vendor
pinouts, external flows). Ergonomics via partiality: declare only
deviations, canonical defaults fill the rest — the empty declaration is
today's behavior, so adoption-v0 is this form's degenerate case. Cost:
the binding-mapping grammar returns (~+3-6d, statement-level, plausibly
simpler than expression literals). Positioning: **adoption stays the v0
floor; declared-binding synthesis is v0.5** — taken when the first group
needs a specific mapping.

*Closure (A36): spec-indexed `WrapField` — A28 reached from the
constructive end.* With declared mappings in hand, `WrapField` becomes
`PortSpec → (field → ports, ports → field)`: the declared clause *is*
the A28 description, `WrapField` its interpreter, and **applying
different port specifications yields different mappings of the same
module**. Consequences: (1) binding variance generated *at the
producer* — for re-synthesizable entries, don't adapt B's rendering to
A's, **re-render B under A's spec** (exact match by construction);
adapters remain for what cannot be re-rendered (imports, sealed
artifacts) — the marshalling layer splits into re-render-when-you-can /
adapt-when-you-must, both spec application; (2) the library already
ships the degenerate form — `ShallowSplit`/`DeepSplit`/`NoSplit` tags
*are* type-level port specifications; A35's declared mappings are the
value-level generalization, bridged per A28's recorded fork;
(3) `WrapInterface`'s pipeline is fully compositional — the spine folds
a spec lookup (declared mapping or canonical default) over the carrier
into spec-indexed `WrapField` leaves, the recording stores the
declaration verbatim, targeting = spec substitution, the round-trip law
holds per (spec, field) by the interpreter lemma — and "forcing"
disappears as a concept: there is only rendering under a given spec.

*A38 — the closure: structure and default naming from types, rendering
overrides from specs, relations from analysis.* The default mapping for
ordinary value types comes from their **`SplitPorts` instances** — and
the instances produce **shape and default names together**, one
deterministic computation (`ShallowSplitPorts'` composes the port name
as it decomposes, appending the field name to the base —
`SplitPorts.bs:66`). The spec's freedom (`WrapField` alternatives,
`NoSplit` vs `DeepSplit`, custom instances, per-port renames) is freedom
*within the type's space of lawful decompositions*: the instance family
enumerates the shapes, the default instance picks one and names it, a
declared spec may pick another and override names — but **a spec can
never conjure a shape the type doesn't admit** (decomposition semantics
type-owned, user-extensible in one place, with round-trip laws; the
application check covers shape only — names are exactly what may freely
differ, per A20). Two claims this grounds: **canonical-by-default's
soundness** — plain same-ifc modules match automatically *because*
names are a pure function computed by the same instance code, a property
of library code rather than parallel convention; and **one naming
grammar, both directions** — the instance's name composition is the
boundary end of A18's propagated selection paths, the same path grammar
running inward and outward from the type structure.
Correspondingly, **application checks the declared skeleton against the
induced decomposition**: per field, declared port count/widths/roles
must unify with the chosen shape; mismatch is a positioned error at the
field's clause, and the message writes itself (the instance family
enumerates the available shapes). Same obligation-pattern as A16's width
micro-contract, one level up — with its value already proven in-project
(v1's boundary width checks caught the real OVL library bug). Import
bindings inherit the identical rigor free: a BVI port clause is a
declared spec for the field's type — the structural check "BVI contracts
aren't clean" was missing.

*A49 — the `synthesize_`-centered MVP (supersedes the adoption/annotation
MVP as the recommended path).* The A42-A48 detour's payoff: **the
primitive gives back the pieces** — feed `synthesize_` a proper
(Synthesizable) thing and the return *is* the contract and mapping,
alongside the `ICVerilog`-shaped `Module b` ("because that is what we
know how to do"). The MVP lives entirely at `b`: group interfaces
written as *primitive* interfaces (port-shaped fields), so `wrap` is
identity and:

```
synthesize_ :: (Synthesizable b) => Module b -> (Module b, IfcContract b, WireMapping b)
mkOneOf_    :: (Synthesizable b) => [(String, Module b)] -> Module b
```

**Acquisition by construction**: the wire map from the unique primitive
decomposition (A45, flat read-off), the contract's elaboration-born half
from the same walk + the field assembler (A48, `impCondOf`), the
analysis-born half appended post-schedule; the `.ba` = the serialized
return (A42). The prior MVP's acquisition machinery — un-join over
residue, symtab name bridge, annotation, peek, witness — is **not
needed, not solved: evaporated by the b-restriction** (and that deleted
work is precisely where the adversarial review located the risk).
**mkOneOf becomes easy**: at the same `b`, binding coherence is
definitional (A43/A45); checks shrink to sched/path refinement (v1's
two); run-and-decorate (A40) remains the mechanism (root runs, instance
decorated, N-ary ifdef + `-use-impl` + manifest). And **the features
unify at `b`**: a BVI import's declared triple compares directly with
computed ones — mixed vendor-IP/BSV groups under one check discipline.
**The one constraint**: MVP group interfaces must be primitive;
rich-typed interfaces need a hand shim — which *is* hand-written `wrap`,
becoming `WrapInterface` instances verbatim. **The upgrade to richer
interfaces is just the `WrapInterface` typeclass, with layered type
errors**: `class (Synthesizable b) => WrapInterface a b` — the law as a
*superclass* — so resolution failure reads "no way to wrap field X"
(missing instance, `a`-level) while `Synthesizable` failure on the
computed `b` reads "your wrapping went wrong at field X" (an instance
produced a non-primitive leaf; the constraint trail names the piece;
instances cannot cheat because the downstream constraint audits their
output, and a bogus instance fails at its own declaration site).
Migration from discipline to machinery is per-interface, incremental,
type-audited. **Estimate ≈10-15 days** — below all previous numbers,
risk flattened. Build list: the two abstract types populated *during*
the existing pipeline at `b` (no convention issues there); `.ba`
carrying the sorted halves; `mkOneOf_`; the printer; the `Synthesizable`
structural check reusing the existing synthesizable-interface
validation. Forward path rework-free: `wrap`/`WrapInterface` later lift
`a`→`b`, `synthesize = unwrap ∘ synthesize_ ∘ wrap`, and the MVP's
primitives are the endgame's primitives.

*The clean MVP path (superseded by A49's b-resident variant; retained
for the rich-`a` fallback).* Where "clean" = nothing built gets retired by the endgame;
everything deferred has a named trigger and remedy. On the v1 branch:
**Step 0** (~1-2d): the half-type design — `IfcContract`/`BoundaryBinding`
as the A32-shaped *sort* of `VModInfo` content (carrier+relations vs
morphism+paths per A30, documented partiality) — the format the endgame
wants, populated from the residue for now. **Step 1** (~3-5d): the
un-join (`contractOf`/`boundaryOf`, same-heap, observer-clean) + the
printer emitting the future literal grammar (today's goldens = tomorrow's
source). **Step 2** (~6-9d): `mkOneOf_` — Id entries (the W8-compatible
permanent form), group adopts the root's recorded binding, exact-match
sound because SplitPorts instances compute shape+names deterministically
(A38), sched/path refinement post-analysis, two-level ifdef macros,
`-use-impl`, manifest; gates: split∘join=id on the group's own instance,
byte-identical default output. **Step 3** (0d compiler): stubs as plain
synthesized modules. **Total ≈13-20 engineer-days, point ≈16 — one
v1-style session-arc.** Deliberately out, with triggers:
`contractOfM`/annotation (first instance-free acquisition need); A35
declared bindings (first non-canonical group — lands as adoption's
generalization, zero rework); round-2 write side, adapters, `WrapModule`
(behind stable seams; the recording-format re-founding rides whichever of
A35/`WrapModule` arrives first). The one judgment call: the MVP reads the
residue (A34) — convention-internal and sound for these operations —
trading the clean morphism now for ~3-6d, defensible because tile grids
never leave the canonical case; paying it now just absorbs into Step 2
without reordering. And to be precise about the GenWrap relationship:
**this is the GenWrap-reusing variant, and the MVP touches zero GenWrap
code** — GenWrap runs unmodified as the incumbent producer (even the
annotation attachment is deferred), while v1's *targeting/forcing*
machinery is not used at all (adoption + A38's deterministic naming
replaced forcing). Of GenWrap's two v1 roles — producer and
forcing-vehicle — the MVP keeps only the first, passively. The
alternative (starting `WrapModule` first) would put W6's enriched Rep on
the critical path, and A31 showed the spine needs Rep content that does
not exist yet — a design project, not a wedge. The quarantine shrinks
the design's contact surface with GenWrap to "reader of its outputs
through endgame-shaped interfaces": every MVP week builds what survives
GenWrap's removal; none extends its reach.

*A40 — adoption corrected to annotation: run the root, decorate its
instance.* GenWrap is not one of the purer stages, and adoption quietly
assumed its recording was the whole boundary realization — it isn't: a
synthesized module is (`VModInfo` + the GenWrap-generated *wrapper code*
with its conversions/plumbing), so a group instance constructed from the
raw recording would present flattened bit-level methods to a parent
expecting user-typed `a`, and supplying conversions means re-generating
a wrapper (generate-mode) or excavating GenWrap's output — the impurity
exactly. The fix is v1's pattern lifted verbatim from imports to BSV
modules: **mkOneOf_ runs the root entry normally** (GenWrap's wrapper
executes unexamined — impurity bypassed by *execution*, the one
operation always safe), **annotates the just-created instance's `vmi`
with the alternates list** (v1's `vFallback` move; interception at
`newState` within a marked dynamic extent — bounded, precedented by
`setBackendSpecific`'s extent marking; a synthesized root's wrapper
creates exactly one foreign instance, so the target is unambiguous), and
**reads recordings only for checks** (root's `.ba` vs entries' `.ba`s —
pure comparisons, no reconstruction). The group's binding never exists
as an input anywhere; it materializes by running the root. Estimate
improves: adoption plumbing deleted, the un-join feeds only
`contractOf`/printer/checks, Step 2 loses its riskiest sub-item, and the
MVP rests on run-and-decorate.

*A41 — the converged MVP signature.*

```
mkOneOf :: (WrapInterface a) => [(String, Module a)] -> Module a
```

Each piece is the settled answer to a fought-through question: the
**`WrapInterface a` constraint** is describe-mode (A39) doing triple
duty — canonical carrier/morphism for checks, `contractOf` typing, and
the printer; fragment gating (no instance → positioned error, not
convention failure); and the pre-laid hook where generate-mode lands
without a signature change. **`[(String, Module a)]`** buys what raw Ids
never could — typechecker-enforced interface compatibility — and under
A40 the *root* (first entry) is a `Module a` in the full sense: it gets
*run* (run-and-decorate needs a runnable value; no peek problem);
non-root entries are required-static top-level references
(name-extracted, positioned error on computed expressions — the
referential-transparency soft spot confined, error'd, and erased when
first-class `Impl` arrives; "Ids with sugar," now justified because the
type does real work). **No contract argument** — consistent with
extraction-only's redefinition of "declare" as freeze-a-reviewed-
extraction: the contract is the root's (run, derived, recorded),
stabilized by golden pinning, with the explicit-contract variant
layering on when a second source exists; in-fragment checks shrink to
schedule and path refinement against the root (bindings
canonical-deterministic per A38) — the two checks v1 already ships. The
MVP in one sentence: **run the first entry, decorate its instance with
the rest, verify refinement, emit the swap** — under a constraint that
names the fragment and pre-books the future.

*A42 — fill mode as a Prelude type.*

```
synthesize :: (WrapInterface a b) => Module a -> (Module b, IfcContract a, WireMapping a b)
```

Not another combinator: **the entire boundary act** — what §3.2 called
the one fill function, what GenWrap + `deffun` + the recording smear
across the pipeline — as one signature, with `(* synthesize *)` demoted
to sugar for top-level application. Three observations: (1) **the `.ba`
is the serialized return value** — the triple (rendered body, semantic
half, wire half) *is* what an artifact records; `VModInfo` = the join of
its last two components; the artifact format becomes the function's
return type — A15's cleanest statement. (2) **The algebra closes at five
verbs over one triple type**: `synthesize` *produces*, `importVerilog`
*forges* (triple with no elaborable body — "contract with no body,"
literally), `mkOneOf` *combines* (entries whose triples must cohere),
`contractOf`/`boundaryOf` *project* recorded ones, `adapt`/re-render
*transforms*. Every feature in this document is one of those verbs.
(3) **The birth-phase axis qualifies the return honestly**: at
elaboration the analysis-born strata (sched, paths) don't exist — as a
*top-level form* `synthesize` denotes the whole per-module pipeline
(triple complete once analysis runs: the recording as it always was); as
an *inline evaluator function* it requires nested `genModule` — W8,
correctly priced there. Indexing: contract at `a` (relations over the
user carrier — parents think in user vocabulary; mkOneOf's constraint
story unchanged), mapping at `a b` (it *is* the morphism between them),
body at `b`; the all-`b` variant is defensible (A23's name-tagged
leaves) with the class transporting relations across the iso —
`WrapInterface a b`, honestly two-parameter with fundep `a -> b`, is the
correspondence carrier: A37's layering clicking into place.

*A45 — primitivity: at a primitive interface, exactly one wire-map
derivation is legal.* The property the two-level structure rests on:
every field of `b` is already port-shaped (name = port name, type =
width, protocol structure = EN/RDY arrangement) — nothing left to
decide. **All rendering freedom is exhausted in the choice of `b`**
(which is what `WrapInterface` instances and specs are); at `b`,
derivation is deterministic. Consequences: (1) `synthesize_` is
choice-free *by theorem* — and A43's exact-match-as-typechecking gets
its real ground: no other derivation exists to disagree with. (2) **The
prescriptive wire map is redundant in artifacts**: the recording needs
only `b` (the type), `vName`, and the analysis-born relations (sched;
paths stay — relations *over* ports, not derivable from shape); the
port map is reconstructible from `b` on demand — `VModInfo` stores port
data today because the flattened type was never the carried source of
truth; under primitivity the type *is* the port map, and
content-addressing cleans up for free. (3) Forged triples validate by
**derive-and-compare**: an import's declared map at primitive `b` must
*equal* the canonical derivation (A38 tightens to equality at the
fragment, the diff as the error). (4) **`Synthesizable`'s content is the primitive decomposition — and the
predicate is the derivation.** Its implementation is a fold over `b`'s
fields reading ports *directly* (name, width, protocol from the shape) —
emphatically *not* `WrapField`, whose job (converting non-primitive
fields to primitive ones) is finished by the time anything is at `b`;
conversion belongs to `wrap` exclusively. The decomposition succeeds
exactly on primitive shapes (a non-port-shaped leaf has no case), so "is
`b` synthesizable" *is* "does the decomposition go through," and its
output *is* the unique map — primitivity as the program's determinism.
Whether it lives as a compiler-derived class in the `Generic` mold
(mechanical instances, resolution failing outside the fragment) or as an
evaluator structural check is an implementation detail: both routes
compute the same object, with the positioned error outside the fragment
falling out either way. Final layering: `wrap` (a→b) = all conversion
and all rendering choice; `Synthesizable`/`synthesize_` (at b) = the
primitive decomposition, trivial, unique, choice-free; analyses = the
relations. Category: **a fake built-in typeclass**, joining bsc's
existing family (`PrimMakeUndefined`/`PrimDeepSeqCond`, and at the far
end the numeric classes) — in the constraint language for signatures and
positioned unresolved-constraint errors, discharged by the compiler's
structural judgment, no user instances; future-proof in that a genuine
extension point could later grow real instances without the constraint
surface moving. The two-class core is thus one *real* class
(`WrapInterface`: user-extensible, all conversion and choice) and one
*fake* one (`Synthesizable`: compiler-judged, choice-free) — the
type-level portrait of the design's oldest slogan: the library owns the
translation, the compiler owns the boundary.

*A46 — the Synthesizable fork dissolved: the gate is the walk, the
decomposition is the walk's output.* Two candidate designs — (A) the
class merely *matches the surface of what the evaluator supports* (a
pure gate), or (B) the class *gives a decomposition* that makes things
easier — resolve as **B implemented by means of A**: the compiler
discharges the constraint by running the evaluator's own structural
acceptance walk and reifies that same walk's result as the class's
decomposition value. One walk, two products (judgment + data); drift
between class and evaluator impossible *by construction*. B's method is
worth having because at `b` it costs almost nothing and feeds almost
everything: reification at `b` is a **flat read-off** (the describe-mode
fidelity risk — A39's prefix composition — lived entirely in the a→b
flattening; at `b` fields *are* ports), and the one value feeds the
printer, `contractOf`'s typing, `mkOneOf`'s comparisons, A45's
derive-and-compare validation, and downstream b2r/SV consumers — the
un-join's cleanest source. It also pre-builds the seam: emission
consuming the reified decomposition (instead of re-walking its own
structures) is the incremental step that makes the class's value the
single source of truth at `b` — A34's quarantine logic applied one level
down, with the oracle equation testable from day one.

*Addendum (the diagnostic argument tips the encoding):* exposing
`Synthesizable` as a **real recursive class over the Rep** (leaf
instances for port-shaped types, mechanically written in the Prelude)
means **the typechecker can always tell you why something is or isn't
synthesizable** — unsatisfiability is a typecheck-time event with a
derivation trail naming the offending piece ("no instance
`PortShaped (FIFO#(t))`, arising from field `enq`"), before elaboration
runs, via existing `ContextErrors` machinery (+ the #286 `TypeError`
hook for prose); and the constraint *propagates*, making generic APIs
self-documenting (`(Synthesizable b) => …` visible in signatures rather
than a latent elaboration surprise). The deference then inverts: **the
class is the spec, the evaluator consumes its decomposition** — the same
single-source guarantee as A46, opposite direction, with the oracle
(evaluator acceptance ≡ class solvability) as the transition test. Leaf
instances carry no bidirectional fundeps, so the #901 solver risk does
not bite. "Fake built-in" resolves to its final form: **real in
mechanism, closed in practice** — combining A's guaranteed agreement,
B's decomposition value, and typechecker-explained failure that neither
had.

*A47 — the typechecker's traversal pays mechanically: instance
resolution compiles the walk.* The class encoding is not merely
diagnostic — resolution *stages* the decomposition (the dictionary's
structure is the per-field walk, composed from leaf instances), and the
evaluator **runs the dictionary once per boundary** instead of
performing its own Haskell traversal. The `iExpandField`-class code
shrinks accordingly: today it re-derives structure from the IType per
boundary (traverse + `IfcBetterInfo` naming + create wires); with the
class, `synthesize_` evaluates the dictionary to the decomposition value
and the evaluator consumes it — **traversal and naming logic move into
instance-resolved library code; the effects (state-var/wire creation,
the irreducible act) stay.** Single-source becomes airtight: boundary
construction consumes *literally the same dictionary* as the checks,
printer, `contractOf`, and A45 validation — divergence inexpressible.
Two qualifications making this a wedge, not a leap: (1) the `b`-level
replacement needs **no enriched Rep** — `iExpandField`'s hard content is
the pragma-fed `a`-level naming that `wrap` owns; at `b` the dictionary
is the flat read-off, so the boundary-construction walk is replaceable
without touching W6/W7; (2) cost is bounded by per-`b` memoization (one
type, one dictionary, one evaluation — the #334 lesson). Conceptual
loop closed: A28's interpreter-over-description and A21's elaborated
compositions meet here — **instance resolution is the fold staged at
typecheck; the dictionary is the interpreter's compiled form**, consumed
by the one place still walking structures by hand.

*A48 — the field assembler as a typed function.* Today `iExpandField`
*is* the per-field assembler (consume the evaluated field + naming info;
manufacture wires, result, EN, and the RDY synthesized from the implicit
condition). The typechecker-driven version makes it a dictionary-supplied
library function — `expandField :: FieldDesc -> f -> AssembledField`
(args/result/en/**rdy** as explicit record components) — with the
evaluator's per-field role collapsing to *call it, register the
results*. Mechanics: (1) **the ready is the crux and its reification
primitive already exists** — `impCondOf`; one companion is needed (a
sharing-preserving guard-splitting primitive), and the fragment condition
making the split well-defined is already a bsc rule (a synthesizable
method's RDY may not depend on dynamic arguments). (2) **§5.2's oldest
promise lands mechanically**: the RDY is a field of the assembler's
return value, not a manufactured stringly sibling; `always_ready` is the
assembler variant that verifies-and-omits it — an instance/spec choice
with a function to be a choice *of*. (3) The duty split is
observer-shaped: library assembles (pure + reification primitives),
evaluator registers (effects). (4) It closes what `b` *is*:
`Module b`'s interface value is literally a record of `AssembledField`s —
`wrap` produces them, `synthesize_` registers them, the primitive
decomposition reads them off; the wrapped type's leaves don't merely
describe the assembler's output type, they *are* it.

*A44 — no descriptions at `a`, ever (supersedes A43's transport clause).*
Contracts and mappings live **only at `b`**; `WrapInterface` provides
*transformations exclusively* (`wrap`/`unwrap` on `Module` values) — the
"transport contracts to user vocabulary" machinery is withdrawn as
invented. Corrected surface: `synthesize :: (WrapInterface a b) =>
Module a -> (Module a, IfcContract b, WireMapping b)` (body back at `a`
for use; descriptions at `b`, the truth about the boundary as built);
`contractOf :: (WrapInterface a b) => a -> IfcContract b` (the fundep
supplies the `b`; "a contract is always a contract for a particular
type" resolves to: *the type is `b`*, with contract-for-`a` well-defined
as contract-at-its-`b`). Reality already agreed: the recording is
`b`-level — `VModInfo`'s flat names are `b`'s members, the relations
range over them. The resulting division is the design's cleanest:
**`Synthesizable b` owns the entire description vocabulary** (defined
once, at the structural fragment, semantics never mentioning
`WrapInterface`); **`WrapInterface a b` owns transformation
exclusively** (relates modules; never produces, consumes, or indexes a
description); one shared law (`WrapInterface a b ⇒ Synthesizable b`),
zero shared vocabulary, no relations crossing the morphism — A30/A32's
non-transportability honored at the type level. User legibility survives
with no `a`-indexed anything: `b`'s leaves are name-tagged with user
field paths (A23/A38), so `b`-level contracts *read* in user vocabulary
without quantifying over user types.

*A43 — the two-step factoring (supersedes A42's indexing note).*
`synthesize` factors into the pipeline's actual structure, typed:

```
wrap        :: (WrapInterface a b) => Module a -> Module b
synthesize_ :: (Synthesizable b)   => Module b -> (Module b, IfcContract b, WireMapping b)
unwrap      :: (WrapInterface a b) => Module b -> Module a

synthesize  :: (WrapInterface a b) => Module a -> (Module a, IfcContract a, WireMapping a b)
synthesize   = unwrap ∘ synthesize_ ∘ wrap   -- contract transported by the class
```

with `(* synthesize *)` = sugar for the composite at a top-level
definition — GenWrap's three smeared phases (rewrite-to-flat,
elaborate/schedule at flat, deffun back) given types. Naming per the
house convention (`mkOneOf_`/`FIFOF_`): the underscore form is the
compiler primitive at boundary level; the bare form is its
class-mediated user-vocabulary composite — A42's signature *is*
`synthesize`, with `synthesize_` exposed underneath. The convention now
carries architectural information: underscore = primitive-at-`b`,
bare = composite-at-`a`. What the split
buys: (1) **`synthesize` does no type-level work** — at `b` ("all
bitifiable") the wire mapping is the canonical near-identity (fields
*are* ports), the contract's carrier is `b`'s members, and the
compiler's irreducible act is create-boundary + analyze + report;
`Synthesizable b` is the structural predicate marking wrapping's fixed
points, with the law `WrapInterface a b ⇒ Synthesizable b`. (2) The
indexing debate settles at `b`: outputs honestly artifact-level;
user-vocabulary contracts are the *transport* across the correspondence
— the class's `to`/`from` doing their job in the other direction, not
extra machinery. (3) **Exact-match becomes typechecking**: with `b`'s
leaves name-tagged (A23), port structure and names are in the type —
same `a`, same instance ⇒ same `b` ⇒ same binding *definitionally*;
canonical-by-default (A38) upgrades from empirical determinism to
theorem; residual runtime verification shrinks to the analysis-born
pair (sched/path refinement), irreducible because behavioral. (4) The
verbs re-home: `importVerilog` forges at `b` (where port clauses
naturally live); `adapt` = `unwrapₐ ∘ wrapᵦ` between different `b`s of
one `a`; `mkOneOf`'s coherence condition is "same `b`," stated once, at
the type level.

*A39 — describe-mode `WrapInterface`: the alternative path, viable now.*
The "enriched Rep on the critical path" objection conflated two modes.
**Generate-mode** (produce the wrapped type `w` and the wrapper) needs
the enriched Rep and carries the #901 solver risk — deferred, the real
W6/W7. **Describe-mode** — generically decompose an interface over the
*existing* Rep (`MetaField` names + recursion for nesting), calling the
*existing* per-field machinery (`methodArgBaseNames`/`inputPortNames`)
to compute port descriptors **as values** — is writable today: a
value-level fold with no fundep-computed `w`, dodging the solver
pressure entirely. Delivers (~4-8d): (1) the clean morphism *derived*
within exactly the MVP's domain (fragment = pragma-free interfaces —
`MetaField` lacks pragma content — i.e. the canonical tile-grid case);
acquisition inside the fragment stops reading the residue (evaluate
library code: no module, no `.ba`, no `mkUSId` reverse-engineering —
subsuming the deferred annotation and the witness trick); (2) **the
producer-swap oracle running from day one** — `describe(a) ≡ GenWrap's
recording` over every pragma-free library interface as a mass property
test; the one fidelity risk (the generic walk reproducing GenWrap's
subinterface prefix composition — leaf names agree by construction
post-#729; the spine's joining is what the oracle verifies) is exactly
what it tests; (3) the seed of the real thing — the enriched Rep later
*widens the fragment* (pragma-honoring), same class, and generate-mode
becomes "additionally compute `w`" on a proven decomposition. Revised
recommendation: adoption remains the floor (Steps 0-2); describe-mode is
**Step 2.5**, taken to have MVP contracts derived rather than
residue-read, at the price of owning prefix-fidelity verification.

*The observer discipline (the principle under the kernel's shape):
boundary queries must not perturb the design being compiled.* Contracts
are meta-level data about modules; module-monad effects are object-level
netlist construction; and instantiate-to-extract is rejected because the
extraction leaves a residue — the instance. Exactly three acquisition
routes are effect-free: **Id resolution** (read a recorded artifact —
entries, pinning), **introspection of an instance that exists for real
reasons** (`contractOf` on `a`, same-heap), and **the alternate-handler
peek** (run the computation under an interpretation where effects don't
happen). This retroactively explains the kernel: entries are Ids because
resolution is the effect-free acquisition; pinning reads `.ba`s; the
handler is the *general* mechanism, not a rescue. (A fourth route was
proposed and withdrawn: a non-strict `contractOfRef` reading its
argument's syntactic name — referentially opaque; the same species of
magic this design removes elsewhere.)

*Superseding the handler: `contractOfM` as a forked full evaluation.*
The final mechanism — Ravi's — is cleaner than the handler and completes
the acquisition story: **evaluate the module action to completion, into
a disposable module-monad state, and discard.** The evaluator's state
has two characters: the *heap is pure* (graph reduction, safely shared;
fork-created cells are memoized structure), while the *module-monad
state* (instance registry, state vars, rules, port-type saves) is
design-building. Fork the latter, let effects land in the branch, run
the action fully, and read the boundary off **the evaluation's own
result — its wireinfo/fieldinfo, the module's own interface structure
computed exactly as synthesis computes it.** (An earlier
capture-at-first-`ICVerilog` formulation was wrong in general: the
first foreign bind is the module's own boundary only for the special
wrapper shape; a body instantiating a sub-FIFO first would hand you an
inner primitive's `vInfo`.) No residue, so the observer discipline holds
*by construction*; referentially transparent (evaluates, never sniffs);
and it is literally the front half of nested `genModule` (§4.4), with
even the full-evaluation form precedented — `AAddSchedAssumps` runs
complete nested `iExpand` *and* `aConv` on its closed root. The dropped
M-forms return under their own names with these semantics:
`contractOfM`/`boundaryOfM :: Module a -> …`. Two tiers by argument
closedness: **tier a — closed roots** (top-level Ids, closed
expressions): full nested evaluation, unconditionally sound, +2-4d —
ships in v0 (intercepted at `handlePrim`, which sees the IExpr;
closedness-checked; positioned error otherwise: "captures
elaboration-time state — instantiate and use `contractOf`, or lift to a
top-level definition"); **tier b — heap-entangled arguments**
(`mkTileStub(cfg)`): shared-heap/forked-module-state, requiring the
pure-vs-design-building partition of the evaluator's `G` state
(+3-5d) — the upgrade, buying parameterized alternates. The caveat is
now per *birth phase*: the **elaboration-born** facts (clocks, resets,
ports, field association) come from the forked elaboration directly —
no `.ba` needed, never-synthesized modules included; the
**analysis-born** facts — `vSched` (born in `ASchedule`) and `vPath`
(born in path analysis) — are read from the root's `.ba` when one
exists, honestly absent otherwise. Nested scheduling+path analysis in
the fork is the remaining increment to full nested `genModule`, on the
ladder. v0 gains one primitive and loses its last wart: acquisition
without instantiation, without name-sniffing, without an instance.

*A30 — the corrected factoring: paths belong to the wire side.* The A15
split lands unexpectedly but rightly: **semantic half = scheduling +
clocking/reset association** (consumed by the semantic analyses — rule
ordering, domain checking; meaningful on interface values with no wires
of their own); **wire half = ports, names, kinds, surface types,
witnesses, *and combinational paths*** (facts about the physical
rendering, consumed by wire-level composition — the parent's loop
analysis composes port-pair graphs). The code already agreed:
`vPathInfo = [(VName, VName)]` (`VModInfo.hs:141`) — port pairs, not
method pairs; the earlier method-level restatement was the artificial
move. The decisive argument: **unsafe RWire variants falsify the
paths→ordering correspondence** — the library deliberately ships
primitives where the physical path exists but the declared schedule
refuses the ordering it would suggest — so paths and scheduling carry
independent information and belong to their respective consumers.
Consequences: (i) fixes A21's hand-wave — adapters/marshalling create
wire paths, the rendering owns paths, re-render → recompute; the
semantic contract is untouched under rebinding, as A17/A20 promised;
(ii) the binding's comparison mode is mixed, matching v1's checks
precisely: ports/names/kinds *exact* (v0), paths by *refinement*
(entry's inferred ⊆ group's declared — a pathless stub trivially
refines; parent loop analysis sound under any selection); (iii) the
domain split (semantic vs wire) and the birth split (elaboration- vs
analysis-born) are **orthogonal axes** — analysis-born facts land on
both sides (`vSched` → contract, `vPath` → binding), so the availability
caveat crosses the factoring; (iv) contracts on interface arguments
(A1/§3.5) carry sched+clocking only — paths through an argument are the
parent's rendering concern — simplifying that feature; (v) **in fill mode the
evaluator *computes* the wire mapping — it is not given.** Wireinfo is
an evaluation product of the rendering machinery
(`WrapField`/`WrapMethod`/`SplitPorts` compute port shape and names;
`primMethod`/`saveFieldPortTypes` deliver them; `IfcBetterInfo` feeds
naming inputs); paths are then appended by analysis — both binding
strata are *outputs*, one during elaboration, one after (`deffun`
receives `wire_info`, `sch`, and `pathinfo` post-schedule,
`GenWrap.hs:1454-1459` — the record has always accreted). "The wire
mapping is given" holds in exactly three places: **imports** (declared
`vmi` inside `ICVerilog`), **target mode** (v1's forcing — constraints
injected into the computation), and **ICVerilog-constructing
primitives**, where the con demands a `vInfo`. That last case corrects
the v0 spec: `mkOneOf_` never elaborates a body, so no rendering
machinery runs for it — its binding must be given, and the earlier
"canonical derivation" was wrong. **The group adopts the root entry's
recorded binding** (computed once, by the real machinery, at the root's
synthesis); exact-match compares the other entries' recorded bindings
against the root's; given-ness always traces back to one genuine
computation. Nothing in a module's own elaboration ever consumes its own
paths — they are read by the *parent's* analysis off the completed
record — so path bounds (root's record or the pin) and entry
path-refinement checks live post-analysis, where v1 ran its checks all
along.

*And the lightweight form (final): self-describing wrappers.* The
packs/unpacks/`primSavePortType` surrounding the real `ICVerilog` are
the boundary information *after compilation into code* — but at the
moment GenWrap generated them it held the boundary as data (`deffun`'s
own inputs). Grounded lightweight acquisition = stop throwing that away:
GenWrap attaches the boundary to the wrapper it generates
(`primAnnotateBoundary vmi (action…)`, identity at elaboration), and
`contractOfM` = WHNF to the annotation, read `vmi`, un-join. Effect-free
with no fork machinery (the action, packs and all, stays unevaluated
behind the annotation); semantically grounded, not syntactic (same
GenWrap run, same inputs, atomically; staleness via the `bi_sig` chain —
the wrapper-level instance of the design's record-don't-recover move,
cf. A22 provenance and the recorded binding); referentially transparent
(WHNF, heap-deref honest). Applied arguments (`mkTileStub(cfg)`) WHNF to
the annotation in the current heap without touching the action —
parameterized alternates without the `G`-state partition, deleting the
fork's tier b as a separate item. The fork demotes to the *semantic
definition* and property-test oracle (annotation ≡ fork result) and the
ladder route for never-synthesized modules' analysis-born half. Cost
~2-3d (annotation prim + GenWrap attachment + WHNF peek; `.bo` presence
rides the alternates-list format bump). **Revised v0 estimate: ≈19-27
engineer-days, point ≈23.**

Assembly joins the halves into `VModInfo` (`ICVerilog`); extraction is the
un-join — inverse functions at adjacent `conAp'` cases, so the A15
factoring exists operationally from day one while the stored format stays
conflated. Two revisions settled the entry and binding forms:

- **Entries are qualified Ids, on semantic grounds (the heap-reference
  argument).** A `Module a` value mid-elaboration is a heap-entangled
  monadic computation: reaching a GenWrap-wrapped module's buried
  `ICVerilog` requires *performing* its `PrimModuleBind` chain, and heap
  references make sandbox-and-discard unsound — a partially evaluated
  value is **not portable to a separate evaluation**. So the
  `Module a`-peek forms (`contractOfM`/`boundaryOfM`) are dropped (four
  extraction primitives become two), while the `a`-forms remain sound:
  same-heap introspection rooted at `ICStateVar`, reading what evaluation
  already did. Entry Ids name **top-level definitions — reentrant** from
  the evaluator's perspective (closed ISyntax in `alldefs`,
  heap-independent, freshly instantiable in any context; the
  `AAddSchedAssumps` precedent) — **specialized at the group's type** (the
  contract's phantom pins `a` monomorphic). In v0 resolution degenerates
  to check-type-then-read-artifact (`vName` + `VModInfo` via gen
  ordering/`.ba` — v1's `vFallback` route, no evaluation performed). The
  pair (reentrant top-level def, monomorphizing instantiation) *is*
  (`ICPolySynth` demand, key) from §4.2-4.4: v0 entry resolution is the
  W8 specialization mechanism's degenerate case (memo always hits), so
  the same entry form later accepts polymorphic definitions with zero
  surface change. Third appearance of the serialization principle:
  closures don't cross evaluation contexts; names do (fallback Ids,
  dictionary hashes, now entries).
- **The explicit binding argument and binding *literals* defer** (wire
  variance is out of scope for v0): bindings come from BVI syntax at
  import roots (v1 as-is) and canonical derivation for BSV groups (exact
  match automatic among plain same-ifc modules), so `mkOneOf_`'s binding
  is derived; `boundaryOf` and the printer stay (inspection and freeze).

Pleasing reduction: `primImportVerilog` is the degenerate
single-external-entry group. Day-one addition: a **printer** for the
parseable contract grammar (`-dump-contract`), without which
extract-then-freeze is stranded. Consciously out, recoverable without
surface change: binding literals, explicit-binding `mkOneOf`,
`mkContract` combinators, `` `define `` anchors, N-ary BVI clause syntax,
`genericStub`, manifest redesign.

*Interfaces return to the privileged position (A29).* The language always
claimed interfaces as its central abstraction; the compiler machinery
demoted them (GenWrap derives the ifc syntactically from the module type;
boundary data lives on modules; ifc metadata survives as pragma
plumbing). The kernel inverts this: `IfcContract a` and
`BoundaryBinding a` are interface-indexed, and their shared vocabulary —
what contracts constrain and wire maps render — is the interface's
*fields*. Modules demote to bodies satisfying interface-indexed
specifications; `w`'s leaves are fields (A23); the enriched Rep (§5.1)
is the interface becoming the carrier of its own boundary metadata; and
the interface *declaration* becomes the natural home for declared
defaults (clocking association and naming pragmas already live there —
the one place the current design got the altitude right). This also
explains why interface arguments (§3.5/A1) kept surfacing as the research
edge: with fields as the vocabulary, an interface value carrying a
contract is the *primitive* notion, and "module boundary" is the special
case where the value has a body behind it.

*The uniform currency: every entry must resolve to a recorded boundary.*
With Id entries, `mkOneOf_` reads exactly `(vName, vInfo)` per entry —
branch name, exact-match + refinement checks — resolved through gen
ordering/`.ba` (v1's route, no evaluation), and constructs its *own*
`ICVerilog { vName, vInfo }` (`ISyntax.hs:774-777`) from the contract ⋈
derived binding with the alternates' names attached: one shared state
var, N names. Assembly produces the con, extraction reads it (via
`ICStateVar`), selection resolves names and produces it — "everything is
a recorded `VModInfo` at the boundary" is the evaluator-level restatement
of "backends read only `avi_vmi`." An entry Id that does not resolve to a
synthesized artifact at the group's type (polymorphic in v0,
non-synthesized, wrong interface) is a positioned error. Corollaries:
`` `define `` anchors are a distinct name-only entry kind precisely
because they have no artifact; and split ∘ join = id on the group's own
instance is a free self-consistency property test.

*Grounded effort estimate (2026-07-03; five per-component investigations
against the tree + adversarial review, ~20 file:line spot-checks).*
**30-52 engineer-days on top of v1, point ≈40 (8-9 expert-weeks),
bsc-expert, incl. tests/docs** — approximately 1-1.3 v1-units.
Components: literals+printer 8-14d (the BVI sublanguage does not factor
cleanly — `pMethodVeriProt` mixes contract and binding facts in one
clause; the 730-line BVI assembly in `CVParserImperative.lhs` needs
per-half splitting; `CVPrint`'s printer is ~60-70% reusable but stale and
not round-trip-safe); evaluator primitives 7-12d; N-ary emission 2.5-5d;
Bluesim link 4.5-7.5d; format/fan-out 0.5-1.5d; plus +7.5-18.5d of
cross-component work per adversarial review: (1) **synthesized alternates
are the main use case but arrive GenWrap-wrapped** (`ICVerilog` buried
under `PrimModuleBind` chains — peek-through +2-3d, or import-declared
alternates + a link-time boundary check); (2) **flattened-vs-nested
method names have no owner** (`VModInfo` names are parse-time `mkUSId`
flat; validation reads nested types; the flat-ifc-only descope would
exclude subinterfaces and likely cannot be ratified for tile
interfaces — evaluator subinterface traversal +3-5d); (3) split∘join=id
needs new test infra (no Haskell test framework exists in src);
(4) half-type design negotiation and end-to-end integration testing are
uncounted by per-component construction; (5) v1's refinement comparator
is inferred-vs-declared post-schedule — declared-vs-declared at evaluator
time is adaptation, not reuse; (6) `-dump-contract` of a synthesized
module hooks post-schedule (VSchedInfo exists only after `ASchedule`).
**Post-review resolution (supersedes the descope framing):** neither
descope is ratified; both findings resolve through existing design
decisions. Finding 2: validate flat contract names against the symtab's
*existing* flattened `FieldInfo` view (what `IfcBetterInfo` already
consumes, `IExpand.hs:958`) — nested interfaces fully supported, ~+1-2d
not +3-5d. Finding 1: settled by the heap-reference argument (entries are
qualified Ids; no peek machinery at all, +0.5-1.5d for the resolution
path). Additionally, wire-mapping variance is confirmed out of scope for
v0 — it was never in this estimate (adapters were excluded by invariant),
and its exclusion also defers the binding-*literal* surface and the
explicit binding argument (bindings: BVI syntax at import roots,
canonical derivation for BSV groups), trimming K1 to ~5-9d.
**Revised total: ≈28-40 engineer-days, point ≈33 (6-7 expert-weeks) —
almost exactly one v1-unit.** Delivery model: one to two v1-style
background session-arcs with v1's verification discipline.

*THE MINIMAL PLAN (final recap — start here to execute).* Four pieces on
top of the v1 branch, read-only over boundaries: (1) `IfcContract a` /
`BoundaryBinding a` as Prelude `primitive type`s (`Name__` pattern) + two
`ICon` variants + `GenBin` cases — no literals, no CSyntax; (2) the
un-join, `contractOf`/`boundaryOf :: a -> …` — two `conAp'` cases,
`ICStateVar` root walk, `VModInfo` split, names validated against the
symtab's flattened `FieldInfo` view; (3) `mkOneOf_ :: IfcContract a ->
[(String, ModuleRef)] -> Module a` — Id entries via the `vFallback`
resolution route, exact binding match (canonical derivation) +
declared-vs-declared refinement, one shared instance + alternates list
(one format bump), N-branch two-level ifdef emission, `-use-impl` link
selection, manifest; (4) printer + golden pinning (`-dump-contract` in
the future literal grammar; refinement-directional verify);
(5) `contractOfM`/`boundaryOfM` — instance-free acquisition via
self-describing wrappers (GenWrap attaches the boundary it already holds;
WHNF to the annotation, never entering the action; applied arguments
included; the forked full evaluation is the semantic definition and
oracle; analysis-born half — sched *and* paths — from the root's `.ba`).
Coverage: BVI fallbacks = v1 as-is; tile selection/stubbing = mkOneOf_ +
plain synthesized stubs, per-instance selection free.
**≈19-27 engineer-days, point ≈23** — one v1-style session-arc + short
follow-up, v1's byte-identical-default gate. Nothing open; first task
inside the estimate is the one-time half-type split design (~1-2d).
Sequence: un-join + printer (useful alone) → wrapper annotation +
contractOfM → mkOneOf_ checks → emission/link/manifest → pin-verify.
Deferred without surface change: the forked evaluation (semantic oracle;
never-synthesized modules' analysis-born half via nested
scheduling/paths), round-2 write
side (literals + `primImportVerilog` + A26 + construction validation),
combinators, N-ary BVI sugar, anchors, adapters, W8 polymorphic entries.

*Selection macros: both levels, nested, instance wins.* Each group
instance emits per-instance tests first (`BSV_IMPL_<parent>_<inst>_<name>`
— parent module + source-derived instance name, stable across recompiles
unlike #401's internal suffixes), then module-wide tests
(`BSV_IMPL_<rootVName>_<name>` — keyed by the root's vName, so "stub all
tiles" is one define and every group defaulting to `mkTile` responds),
then the default (root). Surgical overrides beat blanket settings; both
levels always emitted (no option — an option would mean some artifacts
silently lack surgical selection, discovered at use time; which level a
future DV run needs is unknowable at authoring time). Cost is text, not
hardware: unselected branches are preprocessor-eliminated; a 16×16 grid
with three variants is ~1.5k lines of ifdef chain in the grid parent's
`.v` — verbose, harmless, default kept readable by the `else` arm. Honest limit: "instance" means
instance-within-parent-*definition* — Verilog text is shared by all
instantiations of the parent, so true per-hierarchical-path selection is
preprocessor-impossible (sufficient for tile grids, whose parent is
typically instantiated once). **Bluesim is strictly stronger**: link
walks the real hierarchy, so `-use-impl <hier-path>=<name>` does true
per-path selection — a documented asymmetry. The per-instance macro
spellings belong in the sidecar/manifest so scripts never guess them.

*Acknowledged conflation, contained:* v0's contract value is
VModInfo-shaped internally (it rides v1's machinery), so wire /
scheduling / clocking travel in one carrier — but the *surface* is
already stratified: scheduling is the only user-specified layer;
clocking is defaulted (single clock/reset — the tile-grid case;
`clockedBy`/`resetBy` literal declarations are the days-scale multi-domain
extension); and the wire layer is **never user-specifiable** — the
binding is canonically derived and forced (A20 enforced by omission).
Holding that last line is the one discipline that keeps the conflation
temporary: A15 later splits the internal object behind an unchanged
surface (a format bump, not a semantics change). Two wrinkles pinned now:
**paths default to unconstrained, not empty** (`vPath` rides the carrier
and the check is inferred ⊆ declared — a default-empty declaration would
reject any real implementation with combinational paths while stubs sail
through; ⊤ unless declared, tightened via extract-then-freeze), and
**per-layer error attribution** (keep clock/reset association failures in
their own bucket, not folded into generic boundary inequality, so the
factoring inherits clean diagnostics).

Revised minimum: feature 1 = 0 wk; feature 2 ≈ 2-2.5 wk (the `conAp'`
primitives incl. contract-literal validation + N-ary `VMIfDef`/link
generalization + selection flag); anchors ride in the entry
representation (+days). Alternates must be `(* synthesize *)`d and
imported — ordinary. Deferred without loss: N-ary BVI fallbacks,
manifest redesign, attribute-surface sugar over `mkContract`. (Derived
stubs left this list — `genericStub` is library code, A27.)

- **Contract sources.** (1) The BVI declaration — feature 1, N-ary named
  fallbacks: `fallback "soft" mkSoft; fallback "fast" mkFast;` with
  `vFallback :: Maybe Id` generalized to `vFallbacks :: [(String,
  FEntry)]`. (2) The **`contractOf` primitive** — feature 2, selecting
  among Bluespec implementations of the same module: a
  compiler-recognized primitive (the `genC`/`primSavePortType` tradition)
  resolving a qualified module Id to its inferred boundary (same-package
  via gen ordering; cross-package via its `.ba`). Crucially it is
  **type-indexed — a contract is always a contract for a particular
  type**: `contractOf` yields a `Contract ifc` at the source module's
  interface type, so interface compatibility between the contract and
  every group entry is discharged by the *typechecker*; the boundary
  checker only ever sees the schedule/binding refinement questions. (For
  polymorphic modules "a particular type" means a contract per
  instantiation — the family view of §4.3; v0 scopes `contractOf` to
  synthesized monomorphic modules.) `contractOf` is the seed of
  `IfcContract`-as-value: its result is the thing A15 later factors.
- **Entry kinds.** BSV module (targeted + verified; Bluesim-able);
  **external anchor** — an entry that resolves to a `` `define ``: the
  branch instantiates a user-nameable macro (`` `BSV_EXT_<name> ``) with
  the group's port connections, so something completely different can be
  substituted at simulator/synthesis compile time — unchecked by
  construction, Bluesim-selection is an error, marked `unchecked` in the
  manifest; and (feature 1) the BVI import itself as root/default.
- **Selection.** ifdef/elsif chain on per-name macros
  (`BSV_IMPL_<group>_<name>`), declaration order = priority, final else =
  root; Bluesim `-use-impl <group>=<name>`; `-require-fallback`
  generalizes to `-require-impl`. Default output stays byte-identical
  modulo ifdef lines (v1's regression gate). The parent schedules against
  the group contract only — selection cannot perturb parent scheduling.
- **Steps and rough cost** (atop v1): N-ary fallbacks ~1-2 wk;
  `contractOf` + BSV groups ~2-3 wk; external anchors ~days (carried in
  `FEntry` from the start); `fallback stub;` ~1-2 wk (stub as CSyntax
  generated from the group contract at GenWrap time, normal pipeline;
  precedent `genFuncWrap`, `bsc.hs:377-379`).
- **Forward-compatibility invariants:** selection keys are user-chosen
  Strings (the eventual mkOneOf API); the sidecar-turned-manifest schema
  is versioned and designed once as the A6 seed; parent-schedules-against-
  declared-contract (v1's rule); the group list is the erasure of the
  future `[(String, Impl a)]` — fields get added (A24 witness refs), keys
  never re-shaped; binding variance arrives only as full A17/A21
  replacing forcing wholesale; `contractOf`'s result is what A15 factors.

---

## 4. Specialization-first polymorphic synthesis

### 4.1 The reframing

The wrong question is "how do we synthesize one width-generic netlist?" The
right frame (adopted after the width-generic analysis, §4.6): **a polymorphic
`(* synthesize *)` module is defined by its family of monomorphic
specializations.** This is already bsc's semantics — inlining is
specialization taken to the limit — and each specialization is a plain run of
today's compiler. Under this frame:

- Width-driven elaboration (loop bounds, `valueOf` in expressions, sizing
  state) is *fine* — each specialization elaborates with concrete widths.
- Zero-width ports are *fine* — each specialization drops them through the
  existing `isNotZeroSized` filtering, like any monomorphic module today.
- "Which modules can be width-generic" stops being a language restriction
  and becomes an *applicability test for compression* (§4.6).

The ground truth is always per-point specialization; everything cleverer must
diff-match it (generic-at-N vs direct-specialization-at-N is the correctness
oracle and the CI test).

This answers the tracker's headline synthesis issue directly (#543, "BSC
cannot synthesize polymorphic modules" — whose own suggestion, width as a
Verilog parameter, is rung 4 of §4.6), and several of its satellites for
free: #358 (modules with fully-reducible contexts can't be synthesized — a
module with provisos is the *general* case here; a fully-reducible context is
the degenerate single-key family), #921 (synthesize pragmas at instantiation
sites — demand keys are computed per instantiation anyway; a use-site pragma
is just an explicit demand marker), and #824 (polymorphic `SpecialFIFOs`
vanish from VCDs because they cannot carry `(* synthesize *)` — per-key
boundaries restore hierarchy visibility as a side effect).

### 4.2 Demand: keys computed in the evaluator

Specialization demand is evaluation-driven, not a static scan. A
template-marked definition (marker flows through the `.bo`) becomes a new
ISyntax con — `ICPolySynth`, analogous to `ICVerilog`
(`ISyntax.hs:774-777`). When `conAp'` reaches it with type applications
resolved (the same place `ICVerilog` instantiation happens today,
`IExpand.hs:1377-1408` / `3188`), the **key** is:

```
key = (qualified module Id,
       instantiation of the quantified type variables,   -- numeric + ordinary
       hash of each resolved dictionary tree)             -- §4.3
```

Numeric type-function webs (`TLog`/`TAdd`/`TDiv` relationships among internal
sizes) collapse through the existing numeric normalizer into small keys —
rich internal size relationships reduce to the handful of parameters visible
at the boundary. The evaluator getting *stuck* on an unresolved key component
is an ordinary elaboration error with a position, not a new analysis.

### 4.3 Why dictionaries are hashed, not assumed coherent

BSC typeclasses are **not** globally coherent: orphan instances, overlap
resolved by specificity, no global-uniqueness enforcement. The same
`(module, type-vector)` can bind different dictionaries under different
import graphs, so a type-vector-only cache would conflate different circuits.
The fix is to key on the truth: post-typecheck the call site *is*
`mkFoo @tys dicts`, so the key includes the **resolved dictionary-tree hash**
(recursively over named instance definitions). Consequences:

- Exactly faithful to today's inlining semantics, which already specializes
  per use site with the use site's dictionaries — silently. The key makes it
  visible.
- Coherence demotes from soundness requirement to compression opportunity;
  **incoherence becomes observable** — two same-type-differently-hashed
  artifacts in the cache is the first tooling bsc has ever had for noticing a
  design that disagrees with itself about `Eq#(Foo)`. (Upstream bsc#731 —
  `pack . unpack` not an identity under custom `Bits` — lives exactly here:
  under dictionary-hash keying, the "which Bits did you mean" question has a
  recorded, diffable answer.)
- The key must be *recorded in the parent's `.ba`*: with incoherence
  admitted, types alone no longer reconstruct dictionaries.
- The soundness line, stated once: dictionaries are **nameable, hashable
  values resolved before elaboration** — serializable closures. An
  elaboration-time free variable like SPSRAM's `nwords` captured in a module
  expression is not, which is why arbitrary fallback *expressions* stay out
  of scope (§2) and module *parameters* that should vary per instance must
  cross as real parameters (§7.1) or as key components.
- Honest residue: different dictionaries are genuinely different hardware,
  **including different schedules**. Each key gets its own inferred
  `VSchedInfo`, truthfully. Family-level claims ("schedule uniform across
  all instantiations" — the promise every polymorphic BVI import already
  makes on faith) become an optional declared family contract, verified per
  key by the §3.3 refinement check.

### 4.4 Mechanism: nested, memoized, reentrant genModule

Key → artifact runs as a nested synthesis *during parent elaboration*
(the parent needs the child's boundary and schedule to continue). This is
credible on current evidence:

- `alldefs` already ships full cross-package ISyntax to the evaluator;
  substitution is `eSubst`/`iInst` on values in hand.
- `AAddSchedAssumps.hs:221-239` already runs nested
  `runTI` → `iConvExpr` → `iExpand` → `aConv` mid-compile. The new work is
  factoring `genModule` (`bsc.hs:656`) for reentrancy, not inventing
  reentrancy.
- A **memo table plus demand stack** lives in evaluator state: the stack
  gives cycle detection with a blame chain (A demands B demands A), while
  legitimate self-demand at a *smaller* key (tree reductions, recursive
  interconnect) terminates by decreasing measure.
- **The wrapper already exists.** GenWrap's `deffun` continuation is
  precisely "the expression taking you from the synthesized module back to
  the original type"; nested synthesis calls it with the specialization's
  wireinfo/fieldinfo/schedule. (After §5, this becomes evaluator
  instantiation of `wrapModule` — the per-key `runTI` budget disappears.)
- **Names: the mangled key is the ABI.** Readable for numeric-only keys
  (`mkFoo_10_32`), prefix-plus-stable-hash when dictionaries participate.
  `SPSRAM.bs:73-74` (`"RRSPSRAM_" +++ integerToString nwords +++ ...`) is
  this exact idiom hand-rolled; the feature mechanizes what the library
  already practices, and it resurrects the "computed module names" facility
  principledly (computed names today survive only in Classic
  `module verilog`).

### 4.5 Artifacts: ownership is the design constraint

The dominant cost of per-instance synthesis is not compiler machinery but
**artifact ownership** — everything around `genModule` (orderGens, WrapInfo,
Makefiles, build systems) assumes gens are statically enumerable per package,
and per-demand synthesis makes artifacts materialize during someone else's
codegen. Decisions:

- **In-memory memo + `bdir` as cache.** Key-mangled names; the key and the
  source signature recorded in the emitted `.ba`; staleness via the existing
  `bi_sig`/`bo_sig` chain — **amended (#290):** that chain is demonstrably
  blind to preprocessor macro changes (an `ifdef` flip does not trigger
  recompilation today), so the signature feeding the specialization cache
  must hash the *post-preprocessed* text or include the macro environment,
  or the cache silently serves stale artifacts.
- **Atomic publish, not just determinism (#49) — amendment.** "Deterministic
  names make cross-package races benign" protects against divergent
  *results*, not against partial reads or clobbered temp files (the
  historical shared-bdir race was a fixed shared temp name). Memoized
  specialization `.ba`/`.bo` entries are published with unique temp names +
  atomic rename, always.
- **The type-vector + dict-hash key is reconstructible** — a pure function of
  boundary-crossing information, no closure capture — so a build system can
  regenerate any specialization from the parent's recorded keys. This is what
  keeps demand-driven artifacts on the right side of the ownership wall.
- **Enumerable outputs for build systems (#44, #716) — amendment.** Static
  build systems (Bazel, Buck2) want single-shot compiles with declared
  per-command outputs, and demand-driven specialization makes the artifact
  set *more* dynamic. Two obligations: (i) a machine-readable **manifest** of
  demanded specializations and emitted artifacts per compile — the
  generalization of v1's `.fallbacks` sidecar — plus `-M`-style input lists;
  (ii) a mode where a specialization artifact can be produced by a separate,
  build-system-invoked command from the recorded key (possible precisely
  because keys are reconstructible), rather than only as a side effect of
  the parent's codegen.
- **Bluesim monomorphizes at link time** and must be designed against a
  *build-system-owned* boundary, not bsc-internal link conventions: link
  already walks the hierarchy with concrete method types and owns the simdir,
  so per-width stamping has a natural artifact home — but the interface to it
  (what C++ gets generated where, what can be cached) must be a documented
  contract so an external build system (the Bazel pressure from production
  users; upstream bsc#44) can own C++ compilation and caching. Deliverable: a
  machine-readable manifest of link-generated translation units, stable
  content-addressed names, and no hidden regeneration.
- **Determinism as a tested invariant, not a nicety:** generated `.v`/C++
  must be content-stable so content-hash dedup (§4.6 rung 2) and external
  caches work. The history says this class of bug is real and recurring —
  absolute paths embedded in `.bo`/`.ba` (#191, fixed), nondeterministic
  ISyntax definition order (#627, fixed), recompilation-unstable generated
  name suffixes (#401) — and it silently poisons a content-addressed cache,
  so it needs a CI invariant (bit-identical double-compile), not case-by-case
  fixes.

### 4.6 The compression ladder

Each rung is an optimization over the one below; the bottom rung is ground
truth and the correctness oracle:

1. **Per-point specialization** — always sound, shippable first, and alone it
   already delivers the user-visible feature (polymorphic
   `(* synthesize *)`).
2. **Content-hash dedup** — hash netlists modulo module name;
   `FIFO#(Int#(32)) / FIFO#(UInt#(32)) / FIFO#(Vector#(4,Bit#(8)))` collapse
   whenever only the `Bits` dictionary is consumed. The primitive library is
   the existence proof: one `FIFO2.v` serves every 32-bit type.
3. **Shared front-end** where the family is dictionary/width-uniform — one
   symbolic elaboration + schedule, per-width back-end stamping. This is the
   rung that attacks compile *cost* (the observed pressure: forty widths of a
   big module means forty schedules; scheduling is already superlinear on
   method-heavy conflict-free interfaces, #219; production reports of one
   link step dominating CI). Far smaller symbolic surface than full symbolic
   codegen.
4. **Parameterized netlist** where width-uniform *and* nonzero-witnessed
   (§6) — the `RegFile.v` form (`parameter addr_width`/`data_width`,
   `RegFile.v:23-26`), emitted mechanically instead of hand-written.

Width-generic elaboration (rung 3-4) is a *fragment*: a numeric tyvar stays
free only while phantom through elaboration — the moment `valueOf(n)` reaches
a value/loop bound/slice/structure, the width chooses the circuit. The
fragment check is free (the evaluator gets stuck at symbolic-width value
positions — an error with a position, not an analysis), and the first
prototype step is exactly that check, run over the base library to measure
what share qualifies. Scheduling inside the fragment is width-independent
except SMT disjointness over width-dependent constants (fall back to
conservative). Bluesim inside the fragment either stamps per width at link
time or generates runtime-width code the way the hand-written primitives do
(`WideData`, `bs_wide_data.h:52`).

---

## 5. Dissolving GenWrap: the one-application injection

### 5.1 Enriched `Rep`/`Meta`: one metadata layer, five consumers

Today's derived generic representation (`Prelude.bs:4537-4569`) carries, at a
field, only a type-level name and index: `data (MetaField :: $ -> # -> *)
name idx = MetaField` (`Prelude.bs:4607`). The interface-declaration pragmas
(`prefix`, `arg_names`, `ready`, `enable`, `always_ready`, `clocked_by`,
`reset_by`) and clock/reset association are *not* in the representation —
which is why flattening/naming/RDY handling cannot yet be written as generic
programs and remain Haskell-side string mangling.

**Design once, for five consumers.** The enriched meta layer (type-level
records on `MetaField`-analogues for interfaces: per-field pragma set,
clock/reset domain association, method arity and kind) is consumed by:

1. **Port shaping** — `SplitPorts` instances read it instead of receiving
   names by plumbing.
2. **Contracts** — §3's `con_fields` is a value-level reflection of it.
3. **SV-type emission** — the SystemVerilog-types integration (emitting
   `struct`/`enum` typedefs matching BSV types) wants exactly this metadata,
   and must remain user-implementable typeclasses (the `WrapField`
   philosophy).
4. **External-metadata derivation** — production users generate `SplitPorts`
   instances from non-BSV type definitions (e.g. a `#[derive(Ports)]` on
   Rust-side types); the enriched Rep must be *constructible from external
   metadata*, i.e. no compiler-private magic in the instances.
5. **Signal-name and value mapping** — tooling that maps hierarchical Verilog
   signals back to struct representations, bluetcl value display (#727), and
   bluetcl enum-encoding recovery (#395) read the same association; the
   hand-maintained external `expandPorts.tcl` port-structure recoverer (#683)
   is the workaround this obsoletes. Boundary-structure preservation (#713)
   is the same demand stated as a feature request.
6. **Cross-language type mirroring (b2r)** — generating Rust (or other
   host-language) equivalents of Bluespec types for typed waveform decoding
   via viewer translator plugins (Appendix B). The reverse direction of
   consumer 4's `#[derive(Ports)]` bridge — one bridge design serves both —
   and a direct client of the recorded method↔port mapping (§3.1.1 point 3).

Two amendments extend the layer's *contents*:

- **An open-ended per-port attribute channel (#445), split into opaque and
  interpreted halves (A16).** Synthesis-tool annotations (`(* keep *)`,
  `altera_attribute`, `chip_pin`) must attach to boundary ports and survive
  to Verilog emission — today only achievable by hand-writing SV and
  BVI-importing it. The enriched Rep and the contract carry a per-port
  annotation slot with two disciplines: **opaque** attributes pass through
  uninterpreted (Clash's `Annotate` is prior art for the type-level
  surface), while **interpreted** annotations carry a verify obligation.
  The motivating interpreted case: **SV packed-type ports** (#713). A packed
  SV type of width N is assignment-compatible with `logic [N-1:0]` — same
  wires, same netlist — so "this port holds `foo_t`" is a presentation-layer
  fact that fits the annotation channel (`VModInfo` width-free, Bluesim and
  elaborate-once untouched), but it is not opaque: the compiler must emit
  the typedef package and *verify* width/layout equality against the
  enriched Rep — an `always_ready`-shaped micro-contract at port
  granularity, generated automatically by the consumer-3 emitter (explicit
  annotation is the override, not the normal usage). Qualifiers: only the
  derived-`Bits` fragment maps (a custom `Bits` instance has no matching SV
  layout — the port stays a plain vector rather than lie about the bits;
  same dictionary caveat as §4.3/bsc#731); tagged unions need a fixed
  padded-union encoding decision; the typedef generator must share the §6
  zero-width filtering, which under specialization-first means per-key
  typedefs named by the same mangled-key ABI and listed in the A6 manifest;
  SV `parameter type` ports are the natural rung-4 pairing but stay opt-in
  on tool-support grounds. Import-side, the same annotation is check-only
  (width equality against the declared boundary — useful against vendor SV
  headers). The crisp scope line: packed types preserve the wire set, so
  they are annotation territory; anything changing the wire set (unpacked
  arrays, struct explosion) belongs to port shaping (`SplitPorts`,
  #339/#458), not annotations.
- **Result-side port splitting (#339, nanavati).** `SplitPorts` as merged
  covers per-*argument* explosion; methods also need multiple *output* ports
  (struct fields / vector elements split without faking conflict-free method
  families that stress the scheduler). The port-shape translation must be
  symmetric, and the boundary representation must drop its
  one-output-port-per-method assumption (`VFieldInfo.vf_output` is
  `Maybe VPort`, `VModInfo.hs:270-286`; `AVInst` likewise) — on both the
  import side and the synthesis side. This is a `VModInfo`/`.ba` format
  change and belongs with the contract object's introduction (§10, W4/W6).

Per-element, type-computed port naming (#142 — `foo1..fooN` from a numeric
type parameter, inexpressible in the fixed pragma grammar) then stops being a
pragma-surface question at all: naming is a generic program the user can
instantiate.

**Interior legibility: propagated selection paths (A18).** SV/b2v types
apply at boundaries only, but the interior stays legible without types
because field selection propagates *names*: `req.addr.bank` flowing through
elaboration leaves defs named along the selection chain — names-as-paths
are the interior's shadow of the boundary's type structure. Three
commitments turn this from heuristic folklore into a property: (i) **one
source for both renderings** — today boundary port names and interior def
names come from different machinery that happens to agree (the flattening
paths vs the evaluator's name-propagation heuristics; `AState.hs:409-412`
is this point made from below); under the enriched Rep the naming generic
programs own the path grammar, so interior `req_addr_bank` and the port
`req_addr_bank` agree by construction. (ii) **Stability** — the propagation
exists but wobbles (#401); the naming consolidation makes selection-path
names stable identities. (iii) **A tie-break policy in the optimizer** —
propagation survives only while the def survives (inlining/CSE/mux-merging
choose one name among merged candidates; `pack`/concat launder structure;
legibility fades with optimization depth, concentrating where debugging
attention concentrates — near boundaries and state): when merging, prefer
selection-path names over synthetic ones, so the structure-bearing name
wins ties. The A11 `(* keep *)` channel remains the explicit escape hatch.
Payoff beyond readability: a stable selection-path name rooted at something
typed (a boundary port via the binding's surface-type field, a register of
known type) lets tooling *infer* interior signal types by walking the path
through the Rep — no per-signal type table (see Appendix B, Tier 3).

**Selection provenance as a primitive annotation (A22) — how SV types
extend through the netlist.** Field selection in ISyntax (`ICSel`, field
Ids in hand) is today lowered to `PrimExtract` at computed offsets — the
name erased exactly when it becomes a bit range. The extension: extract and
concat primitives carry optional provenance — (surface type, field path) —
through the netlist IR. The core stays bit-typed (`ATBit`; this is an
annotation channel, the netlist-level analogue of the binding's
surface-type field, not a re-typing of ASyntax). At emission, a
provenance-carrying extract whose subject has an emitted SV type renders as
a member select (`x.req.addr`, not `x[27:4]`); construction renders as
`'{...}` struct literals — SV selectors on bit strings are their own
primitives, so the backend needs a slightly larger primitive vocabulary and
the SV type system supplies the semantics. Consequences: (i) A21 adapter
glue prints as self-documenting typed SV (`assign b.addr = a.req.addr;`),
and every downstream SV tool independently re-checks the offset arithmetic
against the typedef — a second, free checker for the A16 layout
obligation. (ii) A18 upgrades from names to selectors on the SV path:
interior defs with surviving provenance get packed-type declarations and
member access; provenance decays under optimization exactly as names do,
governed by the same structure-bearing tie-break, degrading gracefully to
numeric ranges. (iii) One annotation serves three renderings — SV member
selects, the b2r Rust mirror (Tier-2 residuals become field accesses, not
bit twiddling), and waveform type inference (a provenance chain is a
recorded selection path, not parsed-name heuristics). (iv) The A16 license
governs uniformly: member-select rendering only where the SV layout matches
the encoding (derived `Bits`; tagged unions via the fixed padded-union
form); custom-`Bits` selections correctly keep numeric ranges — typed
rendering wherever the license holds, truthful bits wherever it doesn't.

### 5.2 The wrapper interface becomes a derived type, not a minted one

With the enriched Rep, the flattened boundary interface is computed by
instance resolution — `Wrapped ifc` via a `WrapIfc ifc w | ifc -> w` class
over the interface's representation — instead of minted as a fresh nominal
tycon by `IfcTRec`/`genTDef` (`GenWrap.hs:174`, `825-843`). Flattening,
naming, and RDY generation become ordinary generic programs
(`ShallowSplitPorts'` over `Meta`/`Conc` already demonstrates the shape,
`SplitPorts.bs:42-85`); ready/enable become explicit typed components instead
of stringly `RDY_`-prefixed siblings; `always_ready` becomes an instance
choice. **VModInfo-in stops needing compiler overrides at all** — targeting
(§3) is passing the contract as an argument into the generic wrapper, which
is what the v1 fallback interceptions were simulating from outside via the
pragma masquerade.

The bug classes this excision closes are concrete and open today:

- #679 — BVI imports inside macros collide, because `IfcTRec` mints the
  flattened tycon keyed by *source position* and two macro expansions share
  one. A derived `Wrapped ifc` has no position-keyed mint to collide.
- #820 — `getSortInfo findField2` ICE from string-prefix flattening
  producing ambiguous same-named `FieldInfo` entries — wrongly an error at
  all, since renaming pragmas disambiguate the actual ports. Generic
  flattening over the enriched Rep is structurally unambiguous and
  pragma-aware.
- #307 / #424 — ICEs when a name lands on the reserved `RDY_` string sibling
  of an (always-ready) method. With ready as a typed component and
  `always_ready` an instance choice, the reserved string namespace is gone.
- #234 — Bluesim emits and calls `METH_RDY` even for proven-always-ready
  methods: the RDY exists as a stringly sibling downstream phases must
  remember to drop. Structurally absent under typed ready components. (Same
  disease family as the `GenWrap.hs:1455` `alwaysEnabled` wrinkle.)
- #420 / #617 — crashes and silent acceptance on `arg_names` arity
  mismatches: typed per-method metadata makes the mismatch a positioned
  error at Rep construction.
- #313 / #383 — the type-function-blindness class (a `SizeOf#(...)` in an
  interface type confuses GenWrap; a reducible method proviso ICEs because
  GenWrap runs before deriving). #383's author proposes the fix this design
  adopts: defer boundary work until after deriving and typecheck. These fall
  to the W5 wedge (flattening post-typecheck) even before the full excision.

**The general form (A28): instance-per-shape becomes
interpreter-over-description.** Eventually the per-field machinery is one
function that takes a reified *description* of a field's boundary and
denotes it as the conversion pair:

```
⟦_⟧ :: FieldBoundary name f w -> (f -> w, w -> f)
```

where `FieldBoundary` is the field's slice of the enriched Rep (name,
pragmas, clock/reset association) joined with its contract fragment and
binding entry, and the pair is computed by one generic fold over the
description's structure — producing/consuming the right ISyntax on each
side (bit-level leaves toward ports, the abstract type's constructors
toward the user). Consequences: **targeting = description substitution**
(`WrapField`'s fundep `name f -> w` becomes "the description determines
`w`" — VModInfo-in at field granularity is passing a different
description to the same interpreter, no overrides); **the round-trip law
is proven once** — a lemma about the interpreter by induction on
descriptions, inherited by every boundary, instead of an unchecked
per-instance obligation; **one description, many interpreters** —
wrap/unwrap is the primary denotation, and the SV typedef/typed port
(A16/A22), the b2r decoder (Appendix B Tier 1 is exactly a second fold),
the stub (the interpretation ignoring its input), the waveform
signal→type entry, and adapters (compose `⟦A⟧.from` with `⟦B⟧.to` —
making A21 totality provable) are folds over the same value; and **user
extension re-enters at the right place** (custom description constructors
with their interpretation — the preserved WrapField escape hatch, while
structured cases stop being hand-written instances). The honest fork is
the description's language: type-level (solver computes `w`; #901-class
expressiveness pressure) vs value-level and staged (the evaluator
consumes description values, `w` stays boundary-internal — the §11
HRT/staging lever; A22's provenance annotations are this idea running in
reverse). Likely both: type-level for what the surface must typecheck,
value-level for what the boundary assembler consumes.

**The missing library piece, named (A31): `WrapInterface`.** §5.2's
`WrapIfc` concretized: a typeclass whose **default implementation does
the generic decomposition** — walk the interface's Rep, `WrapField` each
piece, `WrapMethod` beneath — internalizing the loop GenWrap runs from
outside (per-field constraint emission, `GenWrap.hs:907-921`) and
collapsing the compiler's injection to the single §5.3 application
(`WrapInterface ifc w` is *the* constraint `wrapModule` carries). Its
three prerequisites, in decreasing severity: (1) **the enriched Rep** —
`MetaField` carries name+index only, so without A2/#714's metadata the
generic default cannot compute names or protocol and would re-smuggle
them through the very `IfcBetterInfo` plumbing being deleted (why W6
precedes W7; `WrapInterface` is the consumer that makes W6's design
concrete); (2) **the boundary exceeds the field product** — module
arguments and clock/reset skeleton stay with the boundary assembler
(fields to the library, skeleton to the compiler — consistent with
§5.5's three jobs); (3) **default-with-override is #901 territory** —
the class hierarchy must fit current solver limits or the §11 rank-n
lever gets pulled first. v0 is untouched (it reads recorded bindings,
never generates one); `WrapInterface` is the W6/W7 wedge, with a clean
staging seam: annotation-based `contractOfM` ships first, and when
`WrapInterface` later replaces GenWrap's generation, the annotation's
*producer* changes while every consumer is untouched.

*Naming resolution (A37): `WrapModule` on top, `WrapInterface` as its
core.* The class that sees the whole boundary must be keyed on the
**module signature**, because the argument prefix (parameters, value
ports, legacy clock/reset arguments) is invisible from the interface
type alone: `WrapModule` decomposes the arguments into carrier members
with morphism entries — absorbing exactly the residual skeleton A31 left
"with the assembler," and shrinking the compiler's irreducible share to
the act of assembly — then delegates the result interface to
`WrapInterface`. The ifc-restricted core stays standalone because two
consumers have no module: interface-value contracts (A1/§3.5) and
connection-side generic `Connectable` (A33). Two further reasons for
module-scoping the top: the **monad dimension** (§5.5's `SynthBoundary`
is a module-type feature, invisible from the ifc — `WrapModule` over
`m a` hosts the `Module`/`ModuleContext`/`ModuleCollect` instances in
one head) and naming convergence (the injection function has been
`wrapModule` since §5.3). The A33 trajectory thins `WrapModule` over
time — clock/reset membership migrates into the interface as
`InputClock`/`InputReset` fields — but parameters never disappear, so
the module-scoped class is the permanent top, progressively thinner.

**Leaves vs spine — the sharpened diagnosis.** "The evaluator computes
wireinfo via WrapField" is true only *leaf-wise*: #729 moved the
per-field conversions (the leaves) into the library, but the
**spine** — which fields exist (syntactic `getArrows` enumeration), the
flattened shape (`flattenFInfs`, the `IfcTRec` mint), the per-field
iteration (GenWrap emits the `WrapField` constraints; the traversal is
Haskell, not solver work), and wrapper assembly (`deffun`) — is still
GenWrap's. The evaluator evaluates hand-generated applications whose
shape *encodes* a decomposition GenWrap already performed: **the
interface is never computed; its decomposition is handed over.** Three
parties, truthfully: GenWrap computes the decomposition, the library
computes the conversions, the evaluator assembles wireinfo from what
the generated code feeds it. §1.3's pre-typeclass residue list *is* the
spine, exactly — four functions, all spine; "the migration stopped
halfway" has a crisp geometry (leaves migrated, spine didn't), and
`WrapInterface`'s generic default is precisely the spine's relocation.
This strengthens W6's spec: the enriched Rep must carry enough to
**drive the spine** — field enumeration with subinterface recursion,
flattening prefix structure, traversal order — not merely decorate
leaves; the `Meta`/`MetaData`/`MetaConsNamed` machinery has the right
shape, the content is what's missing.

**A32 — the cleaner view: two carriers and a morphism.** The unifying
restatement: **the semantic domain is the field list**, and the
contract's contents are *relations over it* (scheduling: a relation on
`Fields × Fields`; clocking: an assignment `Fields → domains` — nothing
semantic ever mentions a port); **the binding is the morphism** — per
field, its type and port mapping (inputs with types, output, EN/RDY
presence per protocol) — connecting the levels while belonging to
neither; **paths are relations over the port carrier**. A30's
unsafe-RWire argument becomes structural: paths cannot live at field
level because the morphism does not transport relations faithfully in
either direction — the levels are separate *because* the mapping is not
relation-preserving. `WrapInterface` then computes **the carriers and
the morphism, but not the relations**: `fields :: Fields a` (semantic
carrier) and `portMap :: Fields a -> PortMapping a` (the morphism) via
the generic default over the enriched Rep — structural, one answer per
type/rendering — while the relations (sched, clocking, path sets) are
per-implementation or per-declaration *values* over those carriers,
supplied separately as contracts and recorded analysis. `w`, the
conversions, and wireinfo are all *derived* — folds over the computed
description (A28) — rather than primary. The spine (A31) *is*
`fields` + `portMap`; the leaves are the per-field workers the folds
invoke; A15/A23/A28/A29/A30/A31 are projections of this one picture.

*Extension: input clocks and resets are carrier members* — and the
existing code already agrees: `VFieldInfo`'s constructor set is
`Method | Clock | Reset | Inout` (`VModInfo.hs:270-286`), `VArgInfo`'s
is `Param | Port | ClockArg | ResetArg | InoutArg` (`178-185`) — the
carrier existed all along, lacking only the relational reading. The
completed structure: **one heterogeneous carrier** (methods, input
clocks as formal domain variables, resets, inouts, output clocks);
**relations stratified by member kind**, onto which the BVI clause set
maps exactly — `schedule` over methods, `clocked_by`/`reset_by` as
cross-kind assignments, `same_family`/`ancestor` among clock members,
reset synchronicity resets→clocks — so "clocking" stops being an
external domain assignment and becomes internal relational structure;
**the morphism renders each member kind to its port shape** (methods →
data/EN/RDY; clocks → osc/gate; resets → their port) with per-member
partiality expressing the "possible" (Maybe gate, absent reset). This
dissolves most of A31's residual skeleton: clocks/resets/arguments
become ordinary members with ordinary morphism entries; what stays
compiler-side shrinks to value parameters and the assembly act. And the
un-join gets its principled spec: `contractOf` = carrier + member
relations; `boundaryOf` = morphism + port relations — a sort of
`VModInfo`'s existing content by role.

*A33 — `InputClock`/`InputReset`: demand-side types, connection without
arguments.* The carrier view opens the door to **distinct demand-side
types** — `InputClock`/`InputReset` as duals of `Clock`/`Reset`, the
`Get`/`Put` pattern applied to clocking — appearing as ordinary
interface fields, so the hookup is expressed in the expression language
(`mkConnection(clk, ifc.clkIn)` via `Connectable#(Clock, InputClock)`)
and **the argument-passing mechanism disappears**: no `clocked_by`
keyword at instantiation; direction lives in the types. Consequences:
(i) `clocked_by` becomes *interface-internal* — a method's clock
association references a sibling `InputClock` field of the same
interface, giving A32's cross-kind relations their concrete surface,
entirely inside the interface declaration; (ii) **module arguments
shrink toward parameters only** — everything connectable lives in the
interface; (iii) separate compilation already half-agrees: a synthesized
boundary treats input clocks *formally* today (`vClk`'s input list,
bound at instantiation), so only the *association mechanism* changes —
instances are created with unresolved clock sockets, connections unify
them (`primSameClock` over deferred domain variables; unification, not
hardware — you identify domains, you don't drive them), with
resolution-before-analysis (all sockets unified by end of parent
elaboration; unconnected = positioned error or ambient-default) and
connect-exactly-once linearity (the `Inout` member precedent), gating
compatibility as a license-style condition against the clocking
relations; (iv) **bundles compose** — a channel sub-interface carrying
its own `InputClock` means vectors of clocked channels connect
per-element with clocking inside each connection (the tile-grid
per-position clocking case, no per-position argument plumbing); output
direction already works today (exposed `Clock`/`Reset` fields = typed
value passing). Generic `Connectable` over the enriched Rep connects
whole bundles — methods as wires, clock/reset members by unification —
legality checked against both contracts at the connection site. Rides
W6 + the unification primitive; not v0; small *given* the carrier
machinery.

*Completion: the type determines the entire membership.* Methods from
the interface; additional clocks, resets, and value parameters from the
argument signature (`Clock`/`Reset` are already first-class argument
types; parameters already sit there); and the **standard clock and reset
are default members** — present unless the type says otherwise, their
conventional `CLK`/`RST_N` names being merely the *default morphism
entries*. Convention demotes from compiler-ambient machinery to a
defaulting rule over the uniform structure. Consequences: A15 becomes
fully true (contract clocking relations are total over a type-determined
carrier — previously quietly false while the default clock lived outside
the type); #556-class boundary policy ("no clock on these pins") becomes
type-level membership rather than pragma fights; parameters are members
of kind *param* rendering to typed Verilog parameters (A9/A16); and the
Module monad's role clarifies — ambient current-clock/reset threading is
the *use-site* connection mechanism, while the boundary description owns
the members (§5.5's division; `fixupPolyModType`'s hard-substitution is
what erased this distinction).

### 5.3 The injection shrinks to one application

Post-migration, the code GenWrap injects is almost entirely applications of
already-typechecked library functions. So inject exactly one:

```
mkFoo = wrapModule contract mkFoo_
```

with `wrapModule :: (WrapIfc ifc w) => Contract -> Module ifc -> Module w`
typechecked **once, in the Prelude**. Typechecking the injection becomes
solving one constraint at one honest source position — which structurally
fixes boundary-error attribution (today's errors point into generated code;
`ContextErrors` already has the special-casing investment to make one
constraint site readable). The rest of specialization moves to the
**evaluator** — the machinery built for instantiating typechecked polymorphic
code — and the library has half-adopted this already: `WrapMethod`/
`SplitPorts` instances report errors via `primError (getEvalPosition ...)`
at elaboration (`Prelude.bs:4707`).

This also settles the wrapper-lifecycle fork left open in the specialization
design (§4.4): a per-key wrapper is just evaluator instantiation of
`wrapModule` — no per-key `runTI`, no mid-evaluation type minting.

### 5.4 Honest residues

- **Error quality and compile cost** of solver-mediated machinery: no longer
  hypothetical — PR #729's fallout gives the concrete bar. #899 (degraded
  error positions once port names are computed in the evaluator) and #900
  (spurious proviso-failure noise around the real error) are the error-path
  work items; #334 (testsuite time nearly doubled when Generics landed)
  says demand memoization is not optional. A `TypeError`-style user-facing
  mechanism (#286) is a candidate carrier for instance-authored boundary
  errors. Mitigated by dedicated error paths (the `ContextErrors` pattern)
  and memoization; measured, not assumed — the wedge order below keeps a
  bail-out at every step.
- **Solver expressiveness bounds the generic programs**: #901 shows a
  `SplitPorts` helper class (`AppendTuple`) cannot take bidirectional
  fundeps without making instance overlap unorderable. The §5.2 generic
  programs must be designed within current solver limits, or solver work
  must be explicitly budgeted as a dependency.
- **The nominal boundary type in the `.bo`**: parents, bluetcl, and separate
  compilation currently hang off a *named* flattened interface. Structural
  `Wrapped ifc` must be printable and stable across compilers, or a thin
  nominal alias per boundary remains (one `typedef`-shaped tycon, generated,
  but no longer load-bearing for semantics). This is a compatibility
  decision, not a design blocker, and the alias is the conservative default.

### 5.5 Monad-indexed boundaries

Done correctly, the injection point generalizes over the module monad, and
synthesis for extended `Module` monads becomes an instance declaration
rather than a feature request:

```
wrapModule :: (SynthBoundary m, WrapIfc ifc w)
           => Contract -> m ifc -> Module (BoundaryIfc m w)
```

- `Module`: trivial instance — today's behavior.
- `ModuleContext#(c)`: `BoundaryIfc` enriches the wrapped interface with the
  `Expose`d context interface (`ModuleContext.bsv:86-91`); the use site
  reburies via `Hide`/`reburyContext` (`ModuleContext.bsv:135-136`).
  Reification is not a compromise: a side channel *cannot* cross a Verilog
  module boundary; exposing it as ports is the semantics of a boundary for
  that monad — exactly how CBus designs already cross hand-made boundaries.
- `ModuleCollect`: the instance chooses reify-vs-require-completion — the
  first principled home that policy decision has had.

Today `fixupPolyModType` (`GenWrap.hs:581-595`) hard-substitutes `Module` and
erases the possibility; deleting it in favor of the `SynthBoundary`
constraint is the last step of the §5 migration. Everything composes:
contracts apply to exposed context methods uniformly; specialization keys
extend with context types; the fallback swap is untouched (the monad is
compiled away before `avi_vmi`).

**The closing symmetry** — three levels of boundary translation, each a
to/from pair, each library-defined: **field** (`WrapField`, representation),
**port** (`SplitPorts`, shape), **monad** (`Expose`/`Hide`, effect context).
The compiler keeps three jobs: mark the boundary, supply the primitives
feeding the boundary assembler, fill-or-verify the contract after scheduling.

---

## 6. Zero-width ports

Verilog cannot express a conditionally-absent port, and `[N-1:0]` at `N=0`
is a valid *2-bit* range — no single-netlist trick exists. The policy, per
backend and rung:

1. **Bluesim does not have the problem.** Link-time monomorphization drops
   zero-width members exactly as `zeroSizedType` does today
   (`SimPrimitiveModules.hs:72-73`). The discontinuity is Verilog-only, so
   the fix lives in the Verilog artifact story, not in the generic
   representation.
2. **Default rule for parameterized netlists (rung 4): port-reaching width
   tyvars require a nonzero witness** — an `Add#(1, m, n)` proviso, demanded
   by the fragment checker. This keeps the parameterized netlist clean and
   `VModInfo` width-free and structurally stable. The zero case goes where
   bsc has always put it: an unsynthesized polymorphic dispatcher — which is
   *untainted*, unlike `genC`, because dispatching on a type is deterministic
   per instance and backend-identical.
3. **The dispatch is mechanized.** The library hand-maintains exactly this
   today (`FIFO10.v`, `SizedFIFO0.v`, `RWire0.v`, selected by
   `valueOf(sa) == 0` at `FIFOF_.bsv:114` and four sibling sites). A compiler
   that emits `mkFoo` width-generically *derives* the zero specializations:
   re-elaborate with each zeroable tyvar at 0 (ordinary monomorphic
   synthesis; ports vanish through existing `isNotZeroSized` filtering,
   `AVerilogUtil.hs:1034`) and emit `mkFoo_z*` alongside, plus the dispatcher.
   Blowup is 2^k with k almost always ≤ 1, and the variant set is **static —
   known at the module's own compile** — so it stays on the right side of the
   artifact-ownership wall (§4.5).
4. **The discipline extends to boundary *parameters*, not just method ports
   (#550) — amendment.** A concrete `Bit#(0)` module parameter today emits
   `parameter [-1:0] _ = 0'b0` — a valid *2-bit* range — in ordinary
   monomorphic synthesis. `isNotZeroSized`-style dropping (or a
   witness requirement, for the parameterized rung) must apply to
   `vArgs`/parameters as well, and the typed-parameter emission work of
   §7.1 must refuse to render a zero-width range under any circumstances.
5. The industry cop-out (pad to `max(N,1)`, tie off) is available as an
   **opt-in pragma only**: it changes the boundary contract (the port exists
   at zero) and would otherwise poison the width-free `VModInfo`.

The mechanized-dispatch rung has direct open-bug demand: #643
(`mkRegFileFullLoad` silently fails to load when the index type is 0 bits —
a hand-maintained wrapper missing its zero case) is exactly the class the
derived `_z*` specializations close, and the closed history (#836, #839 —
zero-width values inconsistently treated across primitives) is the evidence
that zero flowing through shared code paths is fragile by nature, which is
why the design keeps zero out of the generic netlist *by construction*.

Feature, not bug: zero never flows through the generic netlist; every zero
case is a separately-elaborated, separately-testable artifact; and the
nonzero witness makes the discontinuity part of the *declared* contract.

Note that under specialization-first (§4), rungs 1-3 of the ladder never see
this problem at all — each specialization is monomorphic and zero-width ports
drop per point, exactly as today. The witness rule binds only the
parameterized-netlist rung.

---

## 7. Backend and artifact amendments

Amendments recorded from production experience (MatX sweep) and the upstream
tracker that any implementation must honor:

### 7.1 Typed Verilog parameters

bsc emits module arguments as *untyped* Verilog parameters, and this is
silently wrong in two independently-reported ways:

- **Strings** (MatX #15493): VCS X-2025.06 collapses untyped string
  parameters across instances, silently breaking per-instance `$readmemh`
  preloads.
- **Signedness** (upstream #378): bsc emits unsigned literals (`32'd11`, not
  `32'sd11`) for parameter overrides, and tools infer unsigned for typeless
  `parameter` declarations — silently miscomputing inside BVI-wrapped IP.

**Any design leaning harder on real Verilog parameters** — fallback-only
arguments (§2), parameterized netlists (§4.6 rung 4) — **must emit typed
parameters**: `parameter string`, `parameter integer`/sized declarations,
and correctly signed literals, and must never render a zero-width range
(§6, #550). This is a cheap, standalone fix in the Verilog parameter
emission path and should land before or with the first parameter-heavy
feature. (It also interacts with SystemVerilog output mode: typed parameters
are the SV-native form.)

### 7.2 Build-system-owned Bluesim C++

The link-time-monomorphization story (§4.5) must present a documented,
manifest-driven boundary so an external build system can own C++ compilation
and caching (upstream bsc#44; production Bazel pressure with one link step
dominating CI). Concretely: stable content-addressed names for generated
translation units, a machine-readable list of them, and no regeneration
outside declared outputs.

### 7.3 Deterministic, content-stable output

Version banners/timestamps in generated `.v` defeat content-addressed
caching and rung-2 dedup; make them omit-able (or moved to a sidecar) by
default in cache-relevant paths.

---

## 8. The B-Lang-org/bsc issue sweep

*Method: all 375 issues (217 open, 158 closed) listed via the repo-scoped
API, classified against this design: (a) **absorbed** — the design as stated
answers it; (b) **amendment** — the design changed to accommodate it;
(c) **incidentally fixed** — solved by the fallback branch or a design
component even though unrelated to its motivation; (d) **related** —
supporting evidence or adjacent pressure. 87 issues were relevant (10
amendments, 20 absorbed, 5 incidentally fixed, 52 related); 288 were
orthogonal (build/packaging, parser trivia, features unrelated to synthesis
boundaries).*

### 8.1 Amendments (design changed; folded into the sections cited)

| Issue | What it showed | Change made | § |
|---|---|---|---|
| #44 (open) | Build systems can't enumerate bsc's outputs | Manifest of demanded specializations + `-M`-style input lists | §4.5 |
| #716 (open) | Buck2 wants single-shot compiles, declared outputs | Specializations producible by separate build-system-invoked commands from recorded keys | §4.5 |
| #49 (closed) | Shared-bdir race history | Atomic publish (unique temp + rename) for cache entries; determinism alone is not enough | §4.5 |
| #290 (open) | `bi_sig`/`bo_sig` blind to preprocessor macros | Cache signatures hash post-preprocessed text / macro env | §4.5 |
| #378 (open) | `32'd` vs `32'sd` parameter miscomputation | Typed-parameter work covers signedness + numeric typing, not just strings | §7.1 |
| #339 (open) | Methods need multiple *output* ports | Result-side port splitting; `VFieldInfo`/`AVInst` drop the one-output-per-method assumption | §5.1 |
| #445 (open) | `(* keep *)`/`chip_pin` need a home on ports | Open-ended per-port pass-through attribute channel in Rep + contract | §5.1 |
| #550 (open) | `Bit#(0)` param emits `parameter [-1:0]` | Zero-width discipline extends to `vArgs`/parameters | §6 |
| #631 (open) | `always_ready` blind to RWire internals | Verify mode sees inlineable-primitive definitions (or stages after wire inlining) | §3.3 |
| #658 (open) | BVI port sharing among conflicting methods ICEs | Contract supports many-to-one port mappings conditioned on declared schedule | §3.1 |

### 8.2 Absorbed (the design as stated answers them)

| Issue | Gist | Answered by |
|---|---|---|
| #543 (open) | *The headline*: BSC cannot synthesize polymorphic modules | §4 specialization-first; its own width-as-parameter suggestion is §4.6 rung 4 |
| #358 (open) | Fully-reducible contexts block `(* synthesize *)` | §4.2 — provisos are the general case; keys resolve dictionaries |
| #921 (open) | Synthesize pragmas at instantiation sites | §4.2 — demand keys are per-instantiation already |
| #383 (open) | ICE on method provisos ("genwrap bug"; author proposes deferring past deriving) | §3.2/§5 — the author's fix is the design's pipeline |
| #313 (open) | `SizeOf` in ifc type confuses GenWrap | W5 — flattening on normalized types |
| #282 (open) | Classic imports skip synthesizable-ifc check | §3.1 — one contract validation, two syntaxes |
| #364 (open) | Incomplete `vSched` → uninformative ICE | §3.1 — validation at contract construction, with positions |
| #470 (open) | Attributes on method statements in module bodies | §3.2 phase 1 — per-method contract fragments at marking |
| #545 (open) | Use-side `always_enabled` unenforced | §3.5 — both-direction interface-value contracts |
| #607 (open) | `enabled_when_ready` half-supported | §3.3 — third micro-contract, same mechanism |
| #657 (open) | `chkDupWires` counts RDYs `always_ready` dropped | §3 — one contract consulted by all phases |
| #234 (open) | Bluesim emits/calls RDY for always-ready methods | §5.2 — typed ready components, structurally absent |
| #307/#424 (open) | ICEs on `RDY_` string-namespace collisions | §5.2 — reserved string namespace eliminated |
| #420/#617 (open) | `arg_names` arity: crash (BSV) / silent (Classic) | §5.1 — typed metadata, checked at construction |
| #142 (open) | Type-computed port names (`foo1..fooN`) | §5.1 — naming as a user-instantiable generic program |
| #714 (open) | "Better control of wrapper generation" (pre-#729 proposal) | §5.1 resolves its flagged uncertainties (pragmas in Rep, `MetaIfc`) — closable |
| #713 (open) | Preserve structure at synthesis boundaries | §5.1 port shaping + SV-type emission consumer |
| #643 (open) | `mkRegFileFullLoad` broken at 0-bit index | §6 — derived `_z*` specializations replace hand-maintained zero cases |

### 8.3 Incidentally fixed (solved as a side effect)

| Issue | Gist | Fixed by |
|---|---|---|
| #679 (open) | BVI imports in macros collide (position-keyed minted tycon) | §5.2 — `IfcTRec`/`genTDef` excision removes the mint |
| #820 (open) | ICE from ambiguous string-prefix-flattened `FieldInfo` | §5.2 — generic flattening is structurally unambiguous |
| #824 (open) | Polymorphic SpecialFIFOs vanish from VCDs | §4 — per-key boundaries restore hierarchy visibility |
| #760 (closed) | BVI import trapped by Bluesim's name-keyed primitive table | §2 — fallback resolution is the principled Bluesim path for imports |
| #547 (open) | DReg documented SBR, actual C | §3.3 — declared schedules make documentation checkable (needs library adoption) |

### 8.4 Related (evidence and adjacent pressure, grouped)

- **The GenWrap disease, independently confirmed:** #311/#325 (synonym/
  type-function normalization holes — note these survive *past* typecheck,
  so the post-typecheck pipeline inherits them; hardening the normalizer is
  a W5 prerequisite), #593 (closed; `SizeOf` surviving to post-elaboration
  checks), #975 (deriving over associated type functions generates
  wrongly-typed code — pre-normalization codegen again).
- **Contract/pragma-surface pressure:** #194 (rule attributes trapped in
  syntax), #224 (.bs/.bsv pragma parity), #230 (uniform demotion policy —
  folded into §3.3), #314 (ungated output clocks — contract expressivity),
  #316 (machine-readable schedules — a byproduct of `.ba`-sourced
  contracts), #556 (closed; boundary-level "no clock, no RDY/EN" policy),
  #620 (BH/BVI parity), #637 (user access to RDY — representation
  prerequisite lands in §5.2), #540, #326 (assertion-path inventory), #371
  (Verilog keyword legalization wants naming's single home), #654 (closed;
  naming metadata in the wrong representation).
- **Determinism/cache prerequisites (all reinforcing §4.5):** #191 (closed),
  #401, #627 (closed), #564 (closed; graceful failure on artifact mismatch
  matters more when the bdir is a cache).
- **Bluesim artifact story:** #237 (flattened clock wiring vs per-module
  C++), #376 (version/compatibility checking), #379 (>64-bit index limits in
  runtime-width primitives), #519/#650/#648 (primitive-level Bluesim/Verilog
  divergences — the §4.1 diff-match oracle's substrate must be trustworthy),
  #559 (cross-boundary task-ordering divergence), #323 (Bluesim keys on the
  literal `CLK` string — audit against the "backends read only `avi_vmi`"
  claim).
- **Dictionary/coherence keying (§4.3):** #305 (users want *more* overlap —
  dict-hash keying is load-bearing and pressure grows), #731 (custom `Bits`
  produces genuinely different hardware — the fact the keying is built on),
  #257 (closed) / #293 (dictionary-resolution and instance-nameability edge
  cases the hash must survive), #879 (ValidateBits — another
  library-typeclass-plus-hook client).
- **Specialization staging evidence (§4.2/§4.6):** #169 (per-width DPI
  wrappers — a reuse site for the machinery), #219 (scheduling cost), #583
  (symbolic-parameter ICE that the fragment/stuckness check turns into a
  diagnostic), #809 (params are symbolic at elaboration — the §4.3 staging
  constraint observed in the field), #841 (closed; numeric-normalizer gaps
  the key computation must not inherit), #850 (width-generic demand at the
  BDPI boundary).
- **PR #729 fallout / generics cost (§5.4):** #899, #900, #901, #334
  (closed), #286, #353 (closed; Prelude metadata types must be
  namespace-safe against user code).
- **Zero-width history (§6):** #836, #839 (both closed).
- **Rep-consumer demand (§5.1):** #395, #727, #683, #458 (closed; structured
  views of flat BVI buses = import-side port shaping), #177 (BVI'd SV vs
  xsim link scripts — fallbacks mitigate).

---

## 9. Amendments ledger (consolidated)

| # | Source | Amendment | Lands in |
|---|---|---|---|
| A1 | Long-horizon doc | Contracts attach to interface *values*, incl. interface arguments (declared conflicts on used interfaces are the dual of provided ones) | §3.5 |
| A2 | Long-horizon doc | Enriched `Rep` designed once for all consumers (ports, contracts, SV types) | §5.1 |
| A3 | MatX sweep (#15493) | Typed Verilog parameter emission — prerequisite for parameter-heavy features | §7.1 |
| A4 | MatX sweep (#11788 / bsc#44) | Bluesim link-time artifacts designed against a build-system-owned boundary | §7.2 |
| A5 | MatX sweep (#17125, #1085) | Enriched `Rep` constructible from external metadata (derive-from-outside), +signal-name mapping as a consumer | §5.1 |
| A6 | bsc #44, #716 | Demanded specializations enumerable: per-compile manifest (generalizing `.fallbacks`) + separately-invocable production from recorded keys | §4.5 |
| A7 | bsc #49 | Atomic-publish discipline for shared-bdir cache writes | §4.5 |
| A8 | bsc #290 | Specialization-cache signatures hash post-preprocessed source | §4.5 |
| A9 | bsc #378 | Typed parameters include signedness/numeric typing (extends A3) | §7.1 |
| A10 | bsc #339 | Result-side port splitting; boundary representation drops one-output-per-method | §5.1 |
| A11 | bsc #445 | Opaque per-port pass-through attribute channel in Rep/contract | §5.1 |
| A12 | bsc #550 | Zero-width discipline covers boundary parameters (`vArgs`) | §6 |
| A13 | bsc #631 | Contract verify mode sees inlineable-primitive internals | §3.3 |
| A14 | bsc #658 | Contracts express schedule-conditioned many-to-one port sharing | §3.1 |
| A15 | design discussion (2026-07-03) | `Contract` factored into `IfcContract` (type-indexed semantic value: domains, resets, schedule, method-level paths; lives in `.bo`) × `BoundaryBinding` (per implementation+key method→port mapping with collapse licenses, recorded in `.ba`); `VModInfo` = their materialized join. Prerequisite for A1 | §3.1.1 |
| A16 | design discussion (2026-07-03) | Per-port annotation channel splits opaque/interpreted; SV packed-type port = interpreted annotation with width-equality micro-contract, derived-`Bits` only, per-key typedefs. The SV/b2v type itself lives as a first-class *surface-type* field of `BoundaryBinding` — the annotation is the declaration surface, the binding is the home | §5.1, §3.1.1 |
| A17 | design discussion (2026-07-03) | Interchangeability = contract refinement only; bindings may vary and the compiler injects license-derived hookups. Demotes naming-forcing to an optional feature, upgrades cross-package fallbacks to full support, strengthens rung-2 dedup to modulo-binding | §3.1.1, §2 |
| A18 | design discussion (2026-07-03) | Interior legibility via propagated selection-path names: one naming source for boundary and interior, stable paths (#401), optimizer tie-break preferring structure-bearing names; typed roots + path-walking give inferred interior types for tooling | §5.1, App. B |
| A19 | design discussion (2026-07-03) | The combinator endgame: `mkOneOf :: IfcContract -> [(String, Impl a)] -> Module a` — N-ary fallback with contracts as ordinary values; `wrapModule` is its unary case; first combinator of the boundary algebra | §3.6 |
| A20 | design discussion (2026-07-03) | Governing principle: design for type + schedule/clocking compatibility, never wire compatibility — port names are not API; the semantic ABI is `(type, IfcContract)`; wire coupling only at deliberately frozen edges; adapter generation total over licensed bindings | §3.6 |
| A21 | design discussion (2026-07-03) | Adapters are elaborated function compositions (`toB ∘ fromA`), not wire glue — wires are the constant-folded special case; data plane by round-trip law, control plane stays licensed; bindings record their rendering dictionary tree; static mkOneOf lists keep adapter elaboration at parent compile | §3.1.1 |
| A22 | design discussion (2026-07-03) | Selection provenance as primitive annotation: extract/concat carry (surface type, field path) through the netlist IR; SV emission renders member selects and struct literals; adapter glue prints as typed SV re-checked by downstream tools; same annotation feeds b2r rendering and waveform inference; A16 license governs where it applies | §5.1 |
| A23 | design discussion (2026-07-03) | `Impl a = ∃w. (WrapIfc a w evidence, Module w)`; conversion functions run `a ↔ w` where `w` is the solver-computed wrapped type (leaves = name-tagged bit positions, skeleton = protocol) — never a value-level port list; `BoundaryBinding` is `w`'s value-level shadow; the recorded dictionary tree is the serialized existential witness | §3.6 |
| A24 | design discussion (2026-07-03) | Per-field rendering witnesses: one dictionary reference (name+hash) per binding entry denoting the wrap/unwrap *pair*; bodies never stored; `Nothing` = canonical structural rendering (what BVI bindings implicitly are — backward compatible); rehydrated by the evaluator at adapter elaboration | §3.1.1 |
| A25 | design discussion (2026-07-03) | mkOneOf v0 shortest path: BVI fallbacks = v1 as-is; tile-grid stub selection via evaluator primitives — *specified-first* `IfcContract a` literals (`mkContract`, library values, no parser work; partial + conservative default; extract-then-freeze via `contractOf :: a -> IfcContract a`) consumed by `mkOneOf :: IfcContract a -> [(String, Module a)] -> Module a`, per-instance selection free at call sites, external `` `define ``-anchor entries; v1 machinery reused wholesale | §3.6, §10 W1 |
| A26 | design discussion (2026-07-03) | BVI/Classic successors parse directly into `(IfcContract a, BoundaryBinding)` — one semantic constructor behind three surfaces; closes #620/#282/#364 by construction; import = Impl with no body (`importVerilog`); fallback clause = mkOneOf composition; import validation moves to elaboration (post-typecheck by construction), bypassing `fixCModuleVerilog` | §3.6 |
| A27 | design discussion (2026-07-03) | The implementation floor: `primImportVerilog :: String -> IfcContract a -> BoundaryBinding a -> Module a` — one `conAp'` case doing the A15 join-at-construction into `ICVerilog`; computed names/contracts/bindings become ordinary code; and stubbing is free — `genericStub` is pure library code over `Generic`/`Rep`, verified by mkOneOf against the contract (three-line synthesize wrapper as the pre-W8 residue) | §3.6 |
| A28 | design discussion (2026-07-03) | The general form: instance-per-shape → interpreter-over-description — `⟦_⟧ :: FieldBoundary name f w -> (f -> w, w -> f)`; targeting = description substitution; round-trip law proven once over the fold; one description denotes wrap/unwrap, SV types, b2r decoders, stubs, adapters. The exact-match core is permanent: adapters are a marshalling layer producing conforming wrapper Impls (`adapt`), never a mode of the core | §5.2, §3.6 |
| A29 | design discussion (2026-07-03) | Interfaces return to the privileged position: contracts and wire mappings are interface-indexed and speak about interface *fields*; modules demote to bodies satisfying interface-indexed specs; the ifc declaration is the natural home for declared defaults; interface-value-with-contract is the primitive notion, module boundary the bodied special case | §3.6 |
| A30 | design discussion (2026-07-03) | Corrected factoring: paths belong to the *wire* side (binding), semantic side = scheduling + clocking — unsafe RWires falsify paths→ordering; `vPathInfo` is already port pairs; fixes A21's path hand-wave; binding comparison = exact on ports, refinement on paths; domain and birth-phase splits are orthogonal axes | §3.6 |
| A31 | design discussion (2026-07-03) | `WrapInterface`: the missing typeclass — generic default decomposes the ifc and applies WrapField per piece, relocating the *spine* (enumeration, flattening, assembly — GenWrap's residue exactly) into the library; leaves moved in #729, spine didn't; W6's Rep must drive the spine, not decorate leaves | §5.2 |
| A32 | design discussion (2026-07-03) | Two carriers and a morphism: fields (semantic carrier; sched/clocking = relations over it, with input clocks/resets/params as members and standard clock/reset as *default members* — the type determines the entire membership) → port mapping (the morphism) → ports (paths = relations over them); WrapInterface computes carriers+morphism, relations are per-impl/declaration values; `VFieldInfo`/`VArgInfo` were this carrier all along | §5.2, §3.6 |
| A33 | design discussion (2026-07-03) | `InputClock`/`InputReset` as demand-side types (duals of `Clock`/`Reset`, the Get/Put pattern): clock hookup via `Connectable` in the expression language, no `clocked_by` arguments; interface-internal clock association (sibling fields); connection = domain unification (`primSameClock`, resolution-before-analysis, connect-once linearity); bundles connect with clocking inside; module arguments shrink toward parameters | §3.6 (A32 region) |
| A34 | design discussion (2026-07-03) | The WrapInterface substitute: adoption instead of derivation — the kernel reads the recordings the existing pipeline already produces (group adopts the root's recorded binding; checks compare recordings); fresh-mapping gap bridged by derive-by-synthesizing-a-witness (stub → harvest its recording), self-obsoleting against WrapInterface. GenWrap quarantined, not replaced; recording = residue of the morphism (flat-name-keyed, types in the side table) — v0 coherent because convention-internal end to end | §3.6 |
| A35 | design discussion (2026-07-03) | Declared-binding synthesis: carriers from the type, morphism declared (partial, canonical defaults; BVI-clause syntax; v1's targeting as the application mechanism), relations derived (clocking, scheduling, paths). Solves the A34 residue at the producer (mechanism old, data clean); groups get exact-match by construction; targeting gets its surface. v0.5 — adoption remains the v0 floor and this form's degenerate (empty-declaration) case | §3.6 |
| A36 | design discussion (2026-07-03) | Spec-indexed `WrapField` (`PortSpec → field ↔ ports`) — A28 reached constructively: different specs yield different mappings of the same module; re-render-when-you-can / adapt-when-you-must; `ShallowSplit`/`DeepSplit` tags are the existing type-level degenerate form; "forcing" disappears — there is only rendering under a given spec | §3.6 |
| A37 | design discussion (2026-07-03) | Naming/layering: `WrapModule` on top (keyed on the module signature — arguments, parameters, and the §5.5 monad dimension handled cleanly; absorbs A31's residual skeleton), delegating to `WrapInterface` as the standalone ifc core (needed without a module by A1 contracts and A33 Connectable); A33 thins WrapModule toward parameters-only but never to zero | §5.2 |
| A38 | design discussion (2026-07-03) | The closure: structure *and default naming* from types (SplitPorts instances compute shape and names together — canonical-by-default rests on this; one naming grammar with A18's selection paths), rendering overrides from specs (select shapes, rename ports — never conjure shape), relations from analysis; application checks shape only, positioned errors (A16's pattern; proven by v1's OVL catch); BVI clauses inherit the rigor | §3.6 |
| A49 | design discussion (2026-07-03) | The `synthesize_`-centered MVP: live at `b` (primitive group interfaces), acquisition by construction (the primitive returns the contract and mapping; `.ba` = serialized return), mkOneOf easy (coherence definitional; checks = sched/path refinement; run-and-decorate mechanism), features unified at `b` (BVI triples compare with computed ones); upgrade = `class (Synthesizable b) => WrapInterface a b` with layered type errors; hand shims become instances verbatim; ≈10-15 days | §3.6 |
| A50 | implementation (2026-07-03) | As-built record of the A49 MVP, increments 1–6, with the eight findings the implementation taught the design: A47 half-done upstream (`WrapField` in Prelude); `Synthesizable` = evaluator proxy (`SynthPort` = `Bits`); mediation ≠ boundary crossing (`MediateField`, no `primMethod` decoration); BVI drop-out confirmed (compare args by wire, normalize mult 0/1); RDY reified as boundary methods (folding wanted); canonical `WrapInterface` is a type function — residue is naming `b`, endgame `Wrapped#(a)`; load-bearing semantics choices (alternate args ignored, root's paths/rules carried); deliberate residue list | §12 |
| A51 | design discussion (2026-07-03) | Port arguments excluded from implementation groups: a port argument is an interface argument in degenerate form — its contract (what the implementation assumes about the input: stability, read timing, clocking) belongs to A1's used-interface contracts and is not yet expressible; groups over such boundaries are rejected at formation rather than checked incompletely. Parameters, clock and reset arguments remain covered | §12 |
| A52 | design discussion (2026-07-03) | `Wrapped#(a)` factored precisely: an associated type function (`type Wrapped a = b`, the `Rep` sugar) of a NEW canonical-boundary class `WrappedIfc a b \| a -> b` with auto-derived instances per interface declaration — deliberately not of `WrapInterface`, which stays a *relation* (one `a`, several deliberate renderings; hanging the function there would force tag-newtype fights with the fundep). The canonical `WrapInterface` instance is a Prelude default consuming `WrappedIfc` + generic mediation. Scope is interface-only, coextensive with GenWrap's actual type invention: admitted argument kinds (Clock/Reset/params) are already primitive at type level, port arguments are A51-excluded — so nothing is lost; module signatures generalize later by arrow instances on the same class (A37's WrapModule layering), and A1's used-interface contracts readmit wrapping-for-real argument types as one more instance. Staging: B1 derive-in-parallel + equality assert vs GenWrap; B2 GenWrap consumes the derived decl (`genTDef` deleted); B3 Prelude default, hand instances vanish | §12, §5.2 |
| A53 | design discussion (2026-07-03) | A33 concretized — `InputClock`/`InputReset` as demand-side endpoint types appearing as *interface fields* (the Get/Put pattern): the module creates the endpoint (`mkInputClock`/`mkInputReset(clk)`), clocks internals off its `Clock`/`Reset` view, exports it as a field; the parent connects (`Connectable#(Clock, InputClock)`), connection = domain unification, resolved before clock-domain analysis, connect-once linear, unconnected = positioned error. At synthesis boundaries the field lowers to today's input clock/reset ports — electrically unchanged, legible in the type. Consequences: the module signature collapses (arguments shrink to parameters; `Wrapped#(a)` covers "arguments" because they cease to be arguments; A37's WrapModule thins to parameters+monad as predicted); groups compare input clocks/resets as fields, not via the vArgs special path; contracts can name clock association per method by sibling-field name (A32 realized); default clock/reset become implicit default members eventually. Open: gate story for endpoints, reset-clock binding escape, inline-use unification timing, migration (clocked_by stays, opt-in, same lowering so BVI/old code interoperate). First increment: types + endpoint constructors + boundary lowering at synthesized modules; inline unification second | §12, §3.6 (A33 region) |
| A54 | design discussion (2026-07-03) | `WrapInterface` demoted to scaffolding: likely an implementation detail, possibly the wrong affordance, once A52+A53+A36 land. The evidence: canonical instances carry zero content (finding 6) and vanish under `Wrapped#(a)`; the conversions are wholly computed (generic mediation); and the cited reason to keep it a *relation* — deliberate non-canonical renderings — is A36's territory (renderings selected by *spec*, computed by the one engine; adapters marshal, A28), not a user-declared pair of nominal types. A binary class over two user interfaces invites users to define wrappings between named types when the design wants declarations interpreted by one engine. What survives user-facing: `Synthesizable` (the constraint), `Wrapped#(a)` (the function), contract and spec declarations, `Connectable` (A53 endpoints). What survives internally: the mediation traversal (`WrapIfc'`/`MediateField`) as engine plumbing. Sequencing consequence: B3 should bind `synthesizeIfc`/`mkOneOf` directly to `WrappedIfc` + mediation provisos, not to `WrapInterface`; the class ships in the MVP as tested scaffolding and is removed rather than polished | §12, §5.2 |
| A55 | design discussion (2026-07-03) | The field/parameter joint is a staging theorem: every field kind, provided or demanded, is *late-bound* (runtime interaction; circuits elaborate around unconnected demand fields, connection resolves after — why A53's duals work), while a Verilog parameter is *early-bound* (consumed by elaboration itself; the construction, not the interaction, is parameterized — no connect-later story without staging violence). Hence the end-state module signature `p1 -> … -> pn -> Module a`: parameters (and the monad dimension) are the irreducible arrow-residents, everything else is a field of `a` — A37's "never to zero" made precise. Type-level parameters already live in the interface type (`Counter#(n)`); the residue is the value-level per-instance pre-elaboration constant. Parameters retain a rendering story (A3/A9 typed emission) but never field-hood. Artifacts agree from both ends: Verilog's `#(...)` header vs port list; group selection carries parameters symbolically through the chain | §12, §3.6 (A33 region) |
| A56 | design discussion (2026-07-03) | The demand-side family unified: an *input interface* (used interface as field, A1's object) is a bundle of methods the module calls; every primitive input kind is its one-field degenerate form — input `Bits` value = one value method (A51's port argument, re-derived), input Action = one Action method (genuinely new to Bluespec: today encoded by inversion, module-provides-and-environment-polls — the inversion that kept used interfaces second-class), `InputClock`/`InputReset` = the clocking corner. Lowering is the mirrored port pattern (module drives EN/args, receives RDY) — plain wires; what is new is *reverse scheduling flow*: a demanded Action pulls the environment's schedulability into the module's schedule, so the demand side must be scheduled against a *declared* contract (nothing exists to infer from) and connection requires the provider to refine it — `primImposeContract` on the demand field and `checkAlternate`'s permission-lattice refinement with roles swapped; `Connectable` hookup of dual fields = the group-membership check with sides exchanged. A1 becomes load-bearing at the first input Action, and arrives with its checker already written | §12, §3.6 |
| A57 | design discussion (2026-07-03) | Endpoint naming: the boundary port name of a demand-side endpoint belongs to the *endpoint value*, never the interface field — binder-defaulted through the existing `Name__` machinery (hierarchically prefixed in combinators), explicitly overridable (`mkInputClockNamed`, transformer name arguments). The field is pure transport, so enrichment types (`WithInputClock#(a)`) stack freely without name collisions or flattening ugliness; A20 blesses it (port names are recorded boundary facts, not API), A18 gains one client (endpoint names join the single naming grammar); separate compilation and group conformance untouched (names land in `VModInfo`, clocks already compared by wire) | §12, §3.6 |
| A58 | design discussion (2026-07-03) | The evaluator's true input is the boundary description, not the interface value: the A53 endpoint-through-field design forced a coherence invariant (endpoint exported as field ↔ field backed by endpoint) — two channels, static type vs monadic value flow, carrying one fact; the missing home is the A15 object itself (`IfcContract × BoundaryBinding`, A32's two-sided carrier with provided *and demanded* entries, domains, names) consumed directly, paired with a body that fills provided entries and receives demanded ones. Evidence: `ICVerilog`/BVI/A27's `primImportVerilog` already consume descriptions; the struct-of-lambdas is consumed only at `iExpandIface` (the last GenWrap residue, A47's target); all the MVP's groveling (`findBoundaryInstance`, the wrapper walk) is reverse-engineering descriptions from value encodings, and `contractOf`/`wireMappingOf` reify them after the fact. Consequences: demand entries are description entries (statically visible, A57-named; no runtime endpoint threading, no coherence check); the user interface type — including `WithInputClock` views — is a *projection* of the description (A26's one-constructor-three-surfaces at the module definition); `Module a` is the sugared special case; a module is a function from its demand side to its provide side. Sequencing: increment 7 rebased — first-class description value first, then demand entries, `iExpandField` replacement and the A53 family land on it | §12, §3.6, §5.2 |
| A59 | design discussion (2026-07-03) | The description's ontology: a type-indexed value with reified-type content, valid by construction — types appear as the *index* (`Boundary#(a)`; the tether provisos and type functions act on, never inspected) and as *checked data* (reified `Type` values for payload/surface types, via bsc's existing reflection idiom: `typeOf`/`primSavePortType` — which already records port types into `.ba` side tables — `valueOf`, `stringOf`), never as bound variables: no dependent types, no core existentials. Agreement between index and content is established where the description is built (derived, computed, or declared-and-checked at construction — A26/A27's join; `imposeContract` is the pattern in miniature). Body/description mediation is by type functions on the index (`Demands#(a) -> Module (Provides#(a))`, like `Wrapped#(a)`), while the value carries elaboration-time facts (A57 names, domains, relations). `VModInfo` + the port-type side table is this object in untyped post-hoc form; A58 gives it a typed front door. Rendering witnesses (A23/A24) stay in the binding layer, referenced by name | §12, §3.1.1 |
| A60 | design discussion (2026-07-03) | Encoding calculus for the description's type relationship: per entry the fact is ∃`f w`. (field `n` of `a` : `f`) ∧ `WrapField n f w` — a proper existential-with-constraints encodes it directly; GADTs add only match-time refinement, which no consumer needs (consumers use capabilities via dictionary methods, check reified facts, or lower to ISyntax — none refine a type by matching an entry). bsc has neither feature (`ConcPoly` is the scar tissue; §11's rank-n note is the prerequisite if ever added, and existential constructors — not GADTs — would be the right-sized extension). But the deciding force is *seriality*: the description's home is the `.ba`, and dictionaries cannot cross it — names can (A23/A24's witness tree, rehydrated at elaboration); defunctionalized existentials are what the artifact boundary forces in any language. Enforcement relocates to the two ends: construction (instance resolution over `Rep a` is the existential introduction; the stored result is checked) and use (the CPS/fundep encoding already in the machinery — `MediateField`'s shared `w` never escapes; instance resolution is the unpacker: existential elimination without existential types) | §12, §3.1.1, §11 |
| A61 | design discussion (2026-07-03) | Two corrections to A59/A60: (1) entries are unindexed — `BoundaryEntry` is plain reified data (the entry-level `a` existed only to carry `HasField` evidence, the carried-evidence design already rejected); the index survives as a *phantom brand on the aggregate* (`Boundary a` = branded `[BoundaryEntry]`, earned at construction, doing API-level work — typed `VModInfo`, exactly). (2) The seriality objection applies only to the `.ba`: the `.bo` carries *code* — bsc's class system already crosses compilation units as dictionary defs — so the existential crosses as the compiled wrapper, which is what the GenWrap wrapper already is (increment 3's walk consumes it, implicitly). Hence the *enriched wrapper*: wrapper generation additionally emits an ordinary evaluable def (`boundary_mkFoo :: Boundary (Wrapped Ifc)`) serialized by the existing `.bo` mechanism — no new Bin instances, the evaluator evaluates it; parents consume the description instead of groveling (`findModuleBoundary` → evaluate the sibling def; `contractOf`/`wireMappingOf` read it; demand entries live on it); the defunctionalized residue (`VModInfo`, witness names) remains only in the `.ba` for link-time. Increment 7 re-scoped accordingly — smaller, not larger | §12, §3.1.1 |
| A62 | design discussion (2026-07-03) | Entries stratify: *primitive* entries' meaning is exhausted by data (name, direction, kind, ports, width, domain, mult) — they render directly into the refactored `VModInfo` clause (= primitive entries + relations + name, per A15/A30/A32) and travel in the `.ba` for link-time consumers; *compound* entries require running code (conversions, splits, adapters — ISyntax) and live at the `.bo` level as the enriched wrapper (A61), A24's named-witness case. The strata relate by *normalization*: synthesis evaluates a compound description to its all-primitive normal form — `Boundary a` in `.bo`, `Boundary (Wrapped a)` the normal form, the `.ba` stores normal forms; wrapping is the normalization step, `Wrapped#(a)` its type-level shadow, A45's primitivity the stratum boundary, `Synthesizable a` the all-primitive predicate, A28's interpreter has primitive base cases. Consumption splits on the same line: type-level pairing and contract declaration on the compound stratum (elaboration, `.bo`); refinement checks and selection on the primitive stratum (link, `.ba`) — where increments 3–6 already operate | §12, §3.1.1 |
| A63 | design discussion (2026-07-03) | No language existentials required: compound `BoundaryEntry` uses bsc's established abstract-primitive-type idiom (`Name__`, `Type`, `Rules`, `PrimAction`). Introduction = a typed constructor primitive whose result type erases the hidden variables (`primMkCompoundEntry :: (WrapField name f w) => StrArg name -> EntryFacts -> (f -> w) -> (w -> f) -> BoundaryEntry`) — type erasure at a trusted boundary, with A60's introduction-is-enforcement intact (constraints discharged at the construction site; ill-formed entries unrepresentable). Elimination never occurs at hidden types in surface code: surface consumers read only reified data through typed accessors; the evaluator consumes the conversion code internally at normalization, applying HExpr to HExpr as it already does for `Rules` bodies, `ICMethod` code, and increment 3's unevaluated alternates. Stored conversions are closed monomorphized lambdas serialized as ordinary `.bo` code (A61), re-animated by evaluation on import; A24's name+hash witnesses retreat to the `.ba` level only. GADTs/rank-2/existential constructors genuinely unneeded — no consumer performs the surface unpacking those features make safe | §12, §3.1.1 |
| A64 | design discussion (2026-07-03) | Would language existentials make it cleaner? Only at one internal line: the sole consumer of entries' hidden structure is the normalization engine — users read reified data via typed accessors, tools read the primitive stratum, the `.ba` forces defunctionalization in any language, and the description grammar is deliberately closed at the artifact layer (openness = the arbitrary-conversion payload, already present). Existentials would let the assembler be typed library Bluespec instead of A63 evaluator internals — smaller TCB, ICE-shaped bugs (the `conAp'`/`ICMethod` crash) become type errors, `ConcPoly` likely heals — but the engine bottoms out in primitives regardless (ports/`VModInfo` are evaluator effects), so the line moves rather than vanishes. Against §11's price (context reduction abstracting constraints; representation ripple), the sequencing mirrors the rank-n note: build increment 7 on A63 now; the implementation quantifies the payoff — if the evaluator-internal surface stays a handful of handlePrim cases, existentials never earn their keep. Sharpest form: *statically-shaped* wrapping (generic traversals over `Rep`, field types in view, evidence re-proved per leaf) is already library and gains nothing; existentials would make *dynamically-shaped* — description-consuming — wrapping library too (`genericStub` from a description, adapter generation between descriptions, description-driven testbenches, b2r decoders, the assembler), shrinking the built-in to the effect floor (instantiate, ports, `VModInfo`). Stub generation is the likely first customer and the measurement point | §12, §11 |
| A65 | design discussion (2026-07-03) | The operating plan for description-driven features (A63/A64 as procedure): build on the primitive encoding now. Discipline per feature: if its natural input is *the type*, phrase it statically (a `Rep` traversal — library today, forever): `genericStub`-from-type, canonical wrapping, mediation, `Synthesizable`. Only features whose input is inherently a description value with no type in scope (stub an arbitrary loaded boundary, adapt between two loaded descriptions) become `handlePrim` cases — notice the bucket before writing the case. Count the irreducibly dynamic cases and their bug surface as they accumulate; when they outweigh §11's context-reduction surgery (stub-from-description the likely first data point), add existential constructors. The A63 start is additive, not a dead end: constructors, accessors, generated defs and artifacts are unchanged by the extension — existing `handlePrim` cases migrate to typed library one at a time. The measurement decides; either outcome leaves the design intact | §12, §11 |
| A66 | design discussion (2026-07-03) | Entries carry identity, relations carry connection: a `BoundaryEntry` is a named, typed, directed thing (A57 name, kind, direction, reified payload type, port rendering) holding only facts about itself; *every* cross-entry fact is a relation over the carrier referring to entries by name — clocking (`clocked_by(foo, bar)`), reset association, scheduling (the CF/SB/SBR/C family), domain kinship over clock entries (today's clock_family/ancestors pragmas normalized), and, per A30, paths as relations over *ports* on the far side of the morphism. Today's `VModInfo` is the unnormalized form (vf_clock/vf_reset entry-resident, vSched/vPath external); the A62 refactored clause normalizes fully. Payoff: a contract is a set of relation assertions over named entries, the inferred boundary is another, and every check — imposition, group conformance, demand-side connection (A56, roles swapped) — is set-against-set refinement in one relation language; relations-by-name keep contracts data, artifact-safe | §12, §3.1.1, §3.6 |
| A67 | design discussion (2026-07-03) | Correction to A66's one-language blur — the strata are two, each with its own carrier *and its own relations* (A15 taken structurally): level 1, the Bluespec level: typed named entries with Bluespec-level relations (`clocked_by`, `reset_by`, scheduling, domain kinship) = the contract (`IfcContract`); level 2, the wire level: ports (entry renderings, reached by the A32 morphism) with wire-level relations (combinational paths) = the binding (`BoundaryBinding`), where A16's surface annotations also live — paths are level-2, as A30 said. The implementation already agrees (`checkAlternate`: sched refinement over method names, path refinement over `VName` pairs, separately). Structural payoffs: groups = share level 1, differ at level 2 within refinement bounds; demand-side contracts (A56) are purely level-1, declarable before any implementation exists; the refactored `VModInfo` clause is a two-level record (entries, entry-relations \| morphism \| ports, port-relations), not a flat relation set | §12, §3.1.1 |
| A68 | design discussion (2026-07-03) | The trisection (closing keystone): *contract* — Bluespec-level relations between Bluespec-level entries (what groups share, demand sides declare, parents schedule against); *morphism* — the entry→ports mapping, one arrow with two readings: as code it is the wrapping (compound conversions, `.bo`, the enriched wrapper), as data it is the binding (the rendered port map, `.ba` normal form), connected by A62's normalization — the only layer with a code form; *port-side facts* — paths (and A16 surface annotations) riding with the rendered side, analysis-born and per-implementation, structurally peripheral but operationally load-bearing (path refinement guards combinational cycles the contract level cannot see, A30's original motivation). Every feature is an operation on exactly one layer — imposition/demand declaration on the first, wrapping/`Wrapped#(a)`/normalization on the second, path refinement/annotations on the third — and group conformance spans all three in order | §12, §3.1.1, §3.6 |
| A69 | design discussion (2026-07-03) | The evaluation story, implementable form: *bind the duals, then evaluate the rest*. The only phase boundary is dual-entry binding — demand entries are the module's free inputs, realized entry-directed (today's makeInputClk/argument machinery retargeted; ports created, tokens bound) before anything referencing them is forced. Everything after is one demand-driven graph evaluation with multiple roots: the rules, and the provide entries — whose per-entry iExpandField-equivalent (primitive: take the field; compound: apply the packed conversion, A63; then the A48 assembler) is the *forcing context*, not a phase; bsc's evaluator is already this shape (lazy method bodies under iExpandIface, moduleFix knots, one heap graph — a body/provides barrier would break the knot-tying for free). Port shapes remain description-data, known without evaluation. Open questions, both small: the combinator preservation rule (`fmap wrapIfc`/decoration preserve descriptions — increment 3's walk assumes it; state it) and sibling-def naming/export. Staging: 7a generates the description beside an *unchanged* GenWrap wrapper — purely descriptive, consumption swap only, increments 1–6 as oracle; 7b rebinds the duals and the forcing roots onto entries and shrinks GenWrap, with 7a's descriptions as the equivalence check | §12, §3.6, §5.2 |
| A70 | design discussion (2026-07-03) | The description reduces to two lists — and it is `VModInfo`'s existing bipartition seen at the right level (`vArgs`/`vFields` were the two lists all along; the description-first design lands on the artifact's shape, validating both). The split is by *binding time*, not electrical direction: duals = entries whose meaning the environment supplies (the module's free variables, bound first — A69's phase boundary, the lambda's binders); provides = entries whose meaning the body supplies (the forcing roots). Wire direction is level-2, per the morphism — a provided method contains input wires, a demanded Action output wires, inouts are provides with bidirectional level-2 nature — so mixed-direction entries never confuse the bipartition. Parameters belong to neither list (A55 arrow-residents; they persist only in the level-2 instantiation record). Relations span both lists by name (`clocked_by` typically provide→dual); `Connectable` pairs across them (dual ↔ provide of dual kind); `Demands#(a)`/`Provides#(a)` are the lists' type shadows; the module is `params -> λ duals. (rules, provides)` | §12, §3.6 |
| A71 | design discussion (2026-07-03) | Parameters bifurcate, and constants join both lists: A55 sharpened — a *structure-affecting* parameter (elaboration must consume it) is truly arrow-resident, but an *elaboration-symbolic* one (opaque constant of known type, netlist parameter reference; bsc's static/dynamic discipline is the existing guardrail, ParamChainTest the existing proof) is late-bound by the dual-list criterion: a demanded-constant entry, bound at instantiation like a clock. The arrow holds exactly what elaboration must consume. Dually, *provided constants*: a module exports an elaboration-level value (pipeline depth, address map, latency arithmetic) — closed values are description data (`.bo`; dependency-ordered compilation even gives parents structural use across boundaries for free), values computed from demanded constants are compound entries (code in `.bo`, A61) that parents evaluate against their own bindings — compile-time dataflow through the hierarchy in the description layer, netlist-free unless rendered as a constant port (Verilog has no upward parameter carrier). Excluded, and rejected naturally by binding-time typing: structure-affecting cycles (demanding structurally what is supplied symbolically) | §12, §3.6 |
| A72 | design discussion (2026-07-03) | Provided constants demoted (tempering A71): the computations they would carry are idiomatically type-level and top-down in Bluespec (thread one numeric type through parent and child; A2/numeric kinds cover the real cases), leaving only small residual value (diagnostics, manifests) — and they are *hazardous under selection groups*: selection binds after parent elaboration, so structural use of a member-varying provided constant bakes in one member's value while selection swaps members underneath — exactly the silent breakage this design exists to prevent; pinning by contract would make the export pointless. Demanded constants keep their dual-list place (supplied uniformly to whichever member is selected — no hazard, and they subsume bsc's existing dynamic parameters). Provided constants: possible in principle, out of the MVP, contract-pinned if ever admitted | §12, §3.6 |
| A73 | design discussion (2026-07-03) | Is `BoundaryEntry` the right concept, or just Arguments and Fields? Both, layered: the entry is the formal product (kind × side × name × type × rendering) because real machinery quantifies over side — the kind taxonomy is shared across sides (A56's dualization; the compression), relations span sides (`clocked_by`: field → argument), the refinement checker is side-generic (A56 roles-swapped uses the same lattice), and `Connectable` is the kind-preserving side-flip. Arguments and Fields are the two *projections*: the storage partition (A70's lists — side is never stored or consumed mixed), the evaluator's two machineries (binders vs roots), and the user vocabulary. The invariant either extreme would break: never duplicate the kind taxonomy (a mixed list obscures the bipartition; two bespoke types write the kinds twice). Empty cells (A72's demoted provided constants, etc.) are a validity predicate on the product, not grounds for splitting | §12, §3.6 |
| A74 | design discussion (2026-07-03) | The keystone, closing the arc from A1: *contracts span both arguments and fields* — the contract's relation language has one domain, the whole boundary, and that is the real reason the entry carrier is one concept (A73's shared taxonomy and Connectable symmetry are supporting structure). The bipartition is an evaluation-order fact (A70, binding time); the contract is a semantic fact that ignores it: `process SB mem.write` (provide × demand), `clocked_by(process, coreClk)` (provide × dual), A56's outcall entanglement — expressible only as cross-side relations, living on the boundary, in one namespace (A57). This diagnoses today's bsc structurally: vSched provide-only, clocked_by entry-resident, used-interface arguments contractless — A1's gap was never a missing feature but the absence of the spanning carrier. Checker consequence: refinement runs over the full spanning relation set; the existing lattice machinery extends unchanged (already name-based and side-generic) | §12, §3.5, §3.6 |
| A75 | design discussion (2026-07-03) | Arguments are "always" duals of fields — precisely: dualization is an involution on the kind taxonomy and arguments are exactly the negative-polarity entries (clock, reset, value, Action, interface, constant each pair across sides; inout is self-dual; A72's provided constant is a deliberately uninhabited cell — the dual concept exists, the feature doesn't). The "always" holds because A55/A71 evicted the non-entries first (structure-affecting parameters, the monad — not duals because not entries; the old "module arguments" mixed both populations). The deeper law the flat statement is a case of: with demand fields inside interface types (A53), polarity composes through nesting — demanding a bundle flips every polarity within (its provided method becomes your outcall, its InputClock a clock you must supply): the session-type negation. Demanded interfaces (A56's endgame) therefore need no new semantics — pointwise dualization of the bundle's description, an operation on the two lists | §12, §3.6 |
| A76 | design discussion (2026-07-03) | The final compression — the boundary's kind grammar: `data Field = Clock \| Reset \| Inout \| Method \| Const \| Dual Field \| Interface [Field]`, polarity as syntax. Refinements: (1) it is the kind *skeleton* — nodes carry name (A57), reified payload types, facts, rendering; `Const` occurs only under `Dual` (A72's uninhabited plain cell); parameters and the monad stay outside (A55). (2) The equational theory: `Dual (Dual f) = f` (A75 involution), `Dual (Interface fs) = Interface (map Dual fs)` (session negation — A56's demanded interfaces are literally this equation), `Dual Inout = Inout` (self-duality); normal form pushes `Dual` to leaves. (3) The grammar stores polarity *mixed* — the declaration form (A53, declaration order preserved); A70's two lists are the evaluator's partition of the normalized root by outermost polarity: syntax mixed, operation bipartitioned, each at its layer. The grammar is what `Wrapped#(a)` derivation and the description machinery traverse: leaves = SynthField cases, `Dual` = polarity, `Interface` = nesting with A18/A57 name composition | §12, §3.6 |
| A77 | design discussion (2026-07-03) | The grammar explains the history: evaluation is normalize-then-partition (push `Dual` to leaves — demanded bundles surface as negative leaves with composed names, `Interface` nodes dissolve to prefixes — then bind negative leaves as inputs, assemble positive leaves as forcing roots). And the kind taxonomy stratifies by *contract-richness of the leaf*, which retro-explains bsc's pain distribution: `Clock`/`Reset` leaves carry identity only (a domain token; only cheap structural associations point at them) — hence clock/reset arguments crossed boundaries easily with no contract language; `Method` leaves carry behavior (readiness, the scheduling lattice, A56 entanglement) — positive ones cross via *inferred* contracts (vSched, always existed), negative ones need *declared* contracts (nothing to infer from), which bsc never had — hence its single escape, inlining, and its actual rule that interface/function arguments work only without an intervening synthesis boundary. "Interface arguments were tricky" decomposes without remainder into "negative method leaves require declared contracts": the bundle was never the problem. A56 + A74 close it from both ends | §12, §3.6 |
| A78 | design discussion (2026-07-03) | The endgame discipline: pass the whole contract down, *no inference across boundaries* — completing contract-first. A77's polarity asymmetry becomes historical (inference-as-source was the accident that made provides easy while leaking members' scheduling accidents into parents — the disease imposition already treats); with declared contracts on both signs, inference demotes to the in-module checker and the migration tool (`contractOf` = A25's extract-then-freeze), never escaping. All checks unify into *actual refines declared* over one lattice: module vs own declaration at its compile, group member vs group contract at its compile (the deferred increment-3 idea becomes the norm), environment vs demand at connection. Every interface becomes implicitly a group (contract travels with the interface declaration per A29; all implementations checked against one boundary; mkOneOf = the visible tip of general substitutability; contract deviation = a refined interface type, per A20's semantic ABI). The prize: recompilation stability — within-contract changes cannot ripple. Cost is annotation burden; mitigations already designed (conservative defaults = MVP semantics, A38 canonical defaults, contractOf migration) | §12, §3.6, §3.5 |
| A79 | design discussion (2026-07-03) | Status: fixed point under dialogue. Recent probes compress rather than change (A74 keystone = A1; A75–A76 grammar+equations; A77 explains the history; A78 unifies the checks) — the converged object: one decorated grammar (six constructors, `Dual`, `Interface`, three equations), normalize-bind-force evaluation, `.bo` code / `.ba` normal forms, spanning relations as contracts, one check direction (actual refines declared), no cross-boundary inference, no language extensions required. Open, by kind: *unpinned* — surface syntax for contracts, all names, exact declared-relation vocabulary (RDY folding detail, rules-between, ME/EXT placement); *implementation-decidable* — combinator calculus, sibling-def naming, inline demand binding, polarity-mixed types in the surface checker, description cost at scale, the A64 existential measurement; *use-decidable* — contract ergonomics under A78's annotation burden. Methodology (increment oracles, measured deferrals, opt-in migration) exists so contact refines rather than upends. Expectation: grammar and check-direction survive unchanged; vocabulary and syntax move; nothing between | §12 |
| A80 | design discussion (2026-07-03) | The fixed point reframes the MVP, benignly and retroactively: `synthesize_`'s triple `(a, IfcContract, WireMapping)` was the description's two stratum-projections returned before the one object was named — 7a returns the `Boundary`, with `contractOf`/`wireMappingOf` as its projections. The wire mapping is *residual* in exactly A20's sense: at primitive interfaces it has one legal derivation (A45), computed by canonical defaults (A38/A57), information-bearing only at deviations (frozen edges, bespoke BVI ports, A36 spec renderings) — the contract is the semantic ABI, the mapping an observer's artifact. With teeth: the group conformance check's wire-equality half is a *mechanism-level* constraint (verbatim ifdef instantiation reuse), not semantic — A17 said interchangeability = contract refinement only; adapters (A21/A28) will convert port-shape mismatches from rejections into marshalling. Schedule refinement is permanent; wire equality is the current mechanism's shadow | §12, §3.6 |
| A81 | design discussion (2026-07-03) | The unary fragment: wire-mapping elements are `VFieldInfo`'s purely-wires residue (vf_inputs/output/enable; vf_name is entry identity, vf_clock/reset denormalized level-1 relations, vf_mult a unary property). Ready/enable pragmas are *unary contract terms* over entries — `always_ready(foo)`, `always_enabled(foo)`, `enabled_when_ready(foo)` — same level-1 language as the relations, arity one, carrying *obligation direction*: promises by the provider vs assumptions about the consumer, swapped by `Dual` (A56's role-swap in the unary fragment); refinement is rely/guarantee-signed (strengthen promises, weaken assumptions). Their level-2 meaning is exactly A15's *collapse licenses*: the term licenses port omission (RDY/EN dropped), the rendering consumes the license, the mapping records the collapse — contract above, omission below, morphism between. RDY folding thereby resolves as a normalization, not a feature: `RDY_foo`-as-sibling-method was VModInfo's unnormalized spelling; readiness is the method entry's own protocol, and `RDY_foo` never appears as a contract name | §12, §3.1.1, §3.6 |
| A82 | design discussion (2026-07-03) | Ready is a relation (refining A81): a method entry bundles two interaction aspects — the *offer* (provider-driven: invocability for Action methods, **validity** for value methods) and the *use* (consumer-driven: invoke / sample-and-trust) — and a plain ready signal is the canonical contract sentence relating them: use ⇒ offered, same cycle. This seats readiness in the same relation species as scheduling: permissions over interaction events (CF/SB govern co-occurrence between methods; readiness/validity governs occurrence at all, relative to provider state). A81's unary terms are the degenerate corners (always_ready = constant offer → RDY collapse license; always_enabled = unconditional use, a consumer assumption → EN collapse; enabled_when_ready = consumer guarantees the relation), keeping the rely/guarantee signing as the relation's two ends. Canonical Bluespec rendering is itself a collapse choice per kind: value methods' use-aspect is collapsed (reading is wireless; RDY qualifies the consuming rule), Action methods' is wired (EN). The opened door: Method as micro-bundle (offer, use, payloads — ActionValue the both-payloads case, cf. A10) with a default temporal relation gives A36's renderings their semantic footing — valid/ready streaming (both aspects wired; the consumer's acceptance is its own dual offer), credit (counted permission), fixed-latency are different temporal relations between the same aspects with different wires; renderings become contract-visible, hence comparable and adaptable (A21/A28) | §12, §3.6, §5.1 |
| A83 | design discussion (2026-07-03) | The converged design reorders the implementation payload (same substrate): 7a′ = *declaration-first*, not acquisition-first. The description-as-`.bo`-value remains the substrate, but the first deliverable flips from reading descriptions off implementations to **contracts declared at interface declarations, checked actual-refines-declared at each implementation's own compile** (the A78 wedge) — moving conformance errors from group-formation to member compile, delivering every-interface-is-a-group and ABI stability where MatX needs them, and shrinking the surface: `mkOneOf_ alts root` with the group contract defaulting to the interface's declared one (explicit contract = override; `contractOf` = the A25 migration tool). Schema consequence (A81/A82): the representation is the normalized grammar from day one — entries with offer/use aspects, unary terms, relational clocking — never the triple-list spelling (`RDY_x` names, entry-resident clock association); A80 demotes the mapping to derived rendering data. 7b, demand entries, `Wrapped` sequence behind unchanged | §12, §3.6 |
| A84 | design discussion (2026-07-04) | Naming pinned: **boundary is the place, signature is the object**. The structural half of an interface (entries: fields and arguments, kinds, reified types, port-naming inputs) is its *signature* (`signature_<Ifc>` defs); the behavioral half stays the *contract* (`contract_<Ifc>`, relation sentences over the signature's names); *boundary* reverts to the locus — where a signature is instantiated and rendered to wires (the `.ba`, `VModInfo`, bindings); *protocol* stays reserved for A82's offer/use temporal relations. Signature/contract is the pairing programmers already know (what's there / how it behaves), the ML-module resonance is exact, and the one collision (bsc-internal GenSign package signatures) is never user-facing | §12, §3.1.1 |
| A85 | design discussion (2026-07-04) | Vocabulary stratified within the signature def (clarifying A84): *signature* = level-1 structure only (which fields, what kinds, what types); the field→ports mapping is the *rendering* (the trisection's morphism; A15's binding when realized at a boundary; A80's derived wire mapping). The `signature_<Ifc>` def carries the signature plus the declaration's *rendering directives* — pragma-borne naming inputs (prefix, argN, result) parameterizing the canonical rendering (A38/A57) — which belong in the def as declaration content but are a distinct slot stratum: kind/type = signature; prefix/argN/result = rendering directives; realized wire names = derived, `.ba`-resident | §12, §3.1.1 |
| A86 | design discussion (2026-07-04) | Durability asymmetry and the fencing policy: the rendering vocabulary is already committed for us (twenty years of `import "BVI"` — method/port/enable/ready/prefix/arg_names/result, `VModInfo`'s spelling), so signature-def directive slots keyed to it commit nothing new; the contract language has no fossil record, and its phase-2 string spelling must not ossify by accident. Policy: (1) the string grammar is *frozen* at its three statement forms — future contract features (clocked_by, demand declarations, protocol terms) wait for the typed carrier (the A76 grammar as data) rather than accreting into the string; a three-form grammar migrates by trivial rewrite script; (2) the compiler-internal `DeclaredContract` is the stable interface — the string is a v0 input format, replacement is a parser swap; (3) slot additions stay inside BVI's committed vocabulary | §12, §3.6 |
| A87 | design discussion (2026-07-04) | No textual contract surface at all (superseding A86's items 1–2 before the string ever ships): even a frozen three-form grammar is a premature commitment — text is the most durable artifact a compiler can accept from user code, and surface decisions can't responsibly be made until there is substantial experience *using* contracts. The MVP doesn't need text: the declaration surface is the typed carrier from birth — Prelude `ContractStmt` (constructors `ContractCF/SB/SBR/C m1 m2`, `ContractAlwaysReady m`, `ContractAlwaysEnabled m`, with lower-case builder functions for BSV call syntax), a `contract_<Ifc>` def of type `List#(ContractStmt)` written as a literal list (purely structural reader, no evaluation, computation rejected). What A86 called "the parser swap" happened immediately and *removed* the parser: the compiler-side statement type remains the stable interface; typed carriers evolve through ordinary deprecation (renames and additions produce type errors, not silently-reinterpreted strings). A syntax, if ever, is earned by experience | §12, §3.6 |
| A88 | design discussion (2026-07-04) | The governing separation, restated as the architecture's spine: **the structural stratum is a name-binder** — it exists to establish Bluespec-level entities with, crucially, *names* — the contract world *combines* those names into meaningful sentences, and the rendering maps names to ports. Three worlds, one-directional dependencies: contracts refer to structural names; renderings refer to structural names and may consult contract facts for licenses; the structure refers to nothing. Ports and paths never appear upward (paths are "a side detail that travel with the objects"). Everything already built obeys this: `signature_<Ifc>` is the name-establishing artifact, `contract_<Ifc>` is a list of name-combinations, and the whole enables/readys investigation (A89–A99) changed neither def's job — it enriched the name inventory and the sentence vocabulary, and filed the wires where they belong | §3.1.1, §12 |
| A89 | design discussion (2026-07-04) | Every method carries two derived **facet** events, established by the structure for free: the *offer* (provider willingness — what RDY renders) and the *request* (consumer intent — what EN/valid render), with the committed event **fire = request ∧ offer** (the name is bsc-native: CAN_FIRE/WILL_FIRE). The facets differ in *mode*: an offer is **observed** (value-like), a request is **chosen** (action-like) — which explains the 20-year asymmetry wherein bsc reified readiness as sibling `RDY_m` pseudo-methods (the schedule needs names for things it *reads*) but never reified EN (the schedule speaks of uses natively; scheduling m *is* its request). The conflict relation was bimodal all along, spelled by name-mangling: entries about `m` are statements about request(m)/fire(m); entries about `RDY_m` are statements about offer(m). The normalized language addresses facets of m, never sibling names — the A81/A87 RDY_* ban is this recognition | §3.6, §12 |
| A90 | design discussion (2026-07-04) | **Obligation-site duality**: every contract clause has an obligated party, and is checked at that party's own compile. Provider guarantees (scheduling freedoms, offer constancy) check at each member's compile — built, phase 2. Consumer guarantees (unconditional request) check at each *parent's* compile — and bsc already owns that machinery: an always-enabled method on an instantiated module is a `VPinhigh` port property whose proof obligation (`ProveEq use_expr aTrue`, raised as `EEnableNotHigh`) discharges at the parent. So `contractAlwaysEnabled` lowers onto existing checks the moment sealing stamps the property — zero new checker. The baseline consumer obligation (request ⇒ offered, same cycle) is enforced by the language itself at every call site (implicit conditions ARE that sentence), which is why enables felt invisible: contracts speak only of deviations. Dual entries flip the signs automatically: for an interface argument the module is the consumer, so consumer clauses become member-checked — the checkless architecture needs no new case for duals | §3.6, §12 |
| A91 | design discussion (2026-07-04) | **The factoring theorem**: classic Bluespec enable and retractable valid/ready are the *same semantics with the AND on different sides of the boundary*. Per channel, valid = the rule's complete willingness excluding that channel's own ready (the "but-for" factoring); fire = valid ∧ ready = WILL_FIRE exactly; multi-channel rules generalize (valid_i = φ ∧ other readies; all transfers coincide with rule firing — atomicity preserved; this is literally what EN already encodes, since EN_i = WILL_FIRE ⊇ ready_j). The same-channel AXI law (valid independent of own ready) holds by construction. What the factoring does NOT give: (1) cross-channel combinational dependence (valid_i observes ready_j) — legal per channel but composable into loops/deadlock, which is why AXI ships channel-dependency tables; a *path* fact, see A94; (2) **persistence** — atomic rules retract willingness between cycles by design, so valid-as-factored-willingness may drop before a stalled beat completes; commitment is a genuinely temporal obligation met by construction (a skid/holding stage) or not at all. Hence two disciplines, named per Chisel's precedent (Decoupled/Irrevocable): **retractable** (free, bsc-compatible, the factoring) and **irrevocable/persistent** (costs a register). Every export of ready/valid must say which; "AXI" without a skid is a misnomer | §3.6, §12 |
| A92 | design discussion (2026-07-04) | **The protocol grid**: same-cycle control renders decompose per facet into treatments {raw wire, conjoined event-echo, tied, aliased, absent}, giving the 2×2 of named wires — request raw = Valid, request conjoined = Enable, offer raw = Ready, offer conjoined = **Ack** (Wishbone ACK, OCP SCmdAccept, req/ack handshakes; the fourth corner). Arbiter *grant* is not Ack — it is raw offer with an observation fact (offer observes requests), showing the space is factoring × observation. Beyond the grid: *encodings* of an aspect's information over time — level (Ready), event-echo (Ack), token-delta (**credit**, needing conservation/commitment clauses); stall = polarity directive; almost-full = Ready plus a lookahead clause; **done/response/completion signals are NOT offer variants** — they are second named events with pairing clauses (bursts, out-of-order IDs, sideband errors decompose the same way). Same-cycle adapter inventory is closed: wires, one AND gate, or one skid register. Composition legality: convert at the nearest endpoint, never thread a handshake through a classic boundary (implicit conditions re-introduce the same-channel dependence — classic boundaries are dependence-contaminating, committed endpoints are firewalls). Deliberately split: **boundary contracts** (same-cycle composition facts, v0) vs a future **transaction-contract layer** (credits, bursts, IDs, ordering, response matching) — the temporal protocol world enters later and separately, keeping the clause language from ballooning | §3.6, §12 |
| A93 | design discussion (2026-07-04) | **The coordination theorem (multi-Ack)**: a conjoined offer destroys exactly the information (raw willingness) that a joint atomic decision needs. One Ack participant per rule is free — the ack wire IS the perfect gate (ack = offer ∧ φ = the rule's firing condition; req = willingness-minus-own-offer, same subtraction as A91). Two conjoined-offer participants in one atomic event are impossible in-cycle: the but-for terms close a combinational loop whose only solution is all-zero, and chaining (req₂ = φ ∧ ack₁) silently yields ordered best-effort, not atomicity, because a sovereign provider commits unilaterally with no same-cycle retraction. So the law — at most one conjoined-offer participant per atomic event, any number of raw-offer participants — is a compile-time check with a theorem behind it. The systems reading: this is single-cycle distributed commit; classic Bluespec's architecture (every RDY raw, flowing to the parent, which computes the global decision and broadcasts ENs) is precisely the *coordinator* solution, which is the load-bearing reason Bluespec renders offers raw by default and why multi-method atomic rules are cheap. Relaxing same-cycle turns the loop into a multi-phase protocol (registered ack = response event; reservation/credit/skid) — the same constraint in the time dimension | §3.6, §12 |
| A94 | design discussion (2026-07-04) | **Path/acyclicity unification**: the only primitive composition law is that combinational causality is acyclic. Each factoring choice IS a path declaration (Enable declares offer→request through the consumer; Ack declares request→event through the provider; raw declares no same-channel path); protocol observation laws, the paths renderings imply, and bsc's existing `vPath` are one clause family — **`observes(observer, observed)`** over facets (name chosen so argument order cannot be misread; `vPath` is its port-level shadow). Every matrix result — both-conjoined illegal, multi-Ack, threading contamination, AXI dependency tables, era-1 path refinement — is cycle detection over the union of declared/implied observes facts, so no per-protocol composition rules need hardcoding; bsc's path-graph cycle check is the engine, once implied paths become declared facts. Acyclicity is the same-cycle projection of the deeper requirement that willingness information reach the commit decision before commitment (across cycles it re-materializes as two-phase protocols, per A93) | §3.6, §12 |
| A95 | design discussion (2026-07-04) | **Contracts are relations, period**: every "unary" contract term desugars to a relation with a distinguished or quantified second relatum — `always_ready m` ≡ rel(offer m, ⊤); `always_enabled m` ≡ rel(request m, ⊤) (consumer-signed); effect-freedom ≡ ∀x. CF(request m, x) (the open-world closure, robust to interface extension); persistence ≡ a temporal self-relation (request@t ∧ ¬fire@t ⇒ request@t+1); and **capacity (multi-ported methods) ≡ the counted self-relation** — the diagonal the pairwise language had reserved by excluding self-pairs. Distinguished relata: ⊤, the clock entities, self, future-self, ∀. The diagonal menu has real inhabitants: self-CF = independent capacity (RegFile read banks, indices meaningless, allocator free); self-SB = *ordered* capacity — the CReg/EHR, which BSV could only spell as a Vector of interfaces because the language had no diagonal; self-SBR = ordered, one use per rule (how EHRs are actually used); self-C = the unit (capacity 1, the default — excluded from multi-ported diagonals by arithmetic, not fiat); self-P = coherent, uninhabited, priced by the lattice without needing a ruling. Off-diagonal Boolean, diagonal counted; A82's credit is the counted relation on the time axis. The propositionality divider does the sorting: behavioral truth conditions are relations (find the second relatum or you haven't understood the sentence); the genuinely unary residue is rendering directives. This is the gate the pragma pile never had: **no behavioral flag enters without its relational reading** | §3.6, §12 |
| A96 | design discussion (2026-07-04) | **Renderings**: per-name, non-propositional realization choices — they select among licensed-equivalent realizations and assert nothing (the propositionality divider from A95). Structure: treatments per facet slot (raw/conjoined/tied/aliased/absent), collapses requiring licenses from contract clauses (constancy → RDY absent; effect-freedom → wireless request; unconditional request → EN absent; zero-width → payload absent — §6 becomes a corollary); each choice casts a relational **footprint** (its implied observes facts and obligations) consumed by the global analyses — unary declarations with relational shadows, applied by lookup. The space is a product over slots (merge = per-name override; scoping = longest path prefix; conformance = per-slot diff; BVI = a complete slot map), with aliasing the one binary exception (legacy shared wires; and the legitimate case: enabled-when-ready = request aliased to offer). Renderings **cascade recursively** over the structure tree (inner interfaces travel with their declared renderings, outer scopes override; opaque node treatments — render a subinterface as one typed port — are the b2v future) and **commute with duality**: render(dual f) = dual(render f), the free-connectability theorem — one declared rendering serves both ends of a connection and both polarities of an entry, which is why interface arguments were never supposed to be hard. Implementation ships the simplification: **method conventions** — an enum (`ClassicEnable` default, `ReadyValidRetractable`, later `RequestAck`, `ReadyValidIrrevocable`) on the native primitive `Method ins outs convention mult` — because the space is small and closed, an enum of named points with per-tag footprints beats a combinator language. That primitive is field-for-field the legacy `VFieldInfo`: the old record stored the right things; the design supplies what each field means, which stratum owns it, and who checks it. `mult` is **replication** (rendering; how many port sets are stamped, position-significant under an ordered diagonal, permutable under CF, arrays at typed targets); the *capacity* clause (A95) licenses it; legacy `vf_mult` conflated the two ("0 = unserialized" = capacity ∞ / replication 1, broadcast). Boundary = structure ⊗ wiring, where **wiring is the realized total assignment** (the residue of `VFieldInfo` — A80's wire mapping properly seated) and the declared statements are sparse instructions over canonical defaults, deterministic at the declaration with no member in sight | §3.1.1, §3.6, §12 |
| A97 | design discussion (2026-07-04) | **Names are rooted dotted paths** with derived leaves (facets, payloads, capacity instances): clause atoms reach into subinterfaces (`fifo.enq`), contracts are *relative* formulas over their declaring interface's subtree, and lifting = path prefixing (inner contracts join outer, qualified). The path/underscore split is itself stratified: dotted paths are identity; underscore-joined port names are the canonical *rendering* of hierarchy (what the prefix directives parameterize); an opaque node treatment is a rendering that stops joining. **Honesty amendment (from external critique)**: string method names ARE a textual grammar, however tiny — A87's "no textual grammars" is refined to: no *statement* grammars; v0 admits exactly one checked path grammar, `MethodPath ::= ident ("." ident)*`, documented and error-messaged as such; future surfaces may replace strings with generated path constants. **Aggregate clauses** (deferred until a Vector-bearing contract exists, per A87 discipline) are *required, not sugar*: an interface containing `Vector#(n, …)` cannot enumerate pairs at the declaration because n is a type variable — atoms become path patterns with index variables, and the quantifier inventory is exactly ∀i, ∀i≠j, and a cardinality bound (family diagonal/off-diagonal repeats A95's shape one level up; k-of-n shared capacity; bsc's set-shaped `sME` was always an aggregate clause). Family and capacity are interconvertible views of one indexed namespace (`m.use[i]` vs `bank[i].m` — nesting order), converted by pure renaming | §3.6, §12 |
| A98 | design discussion (2026-07-04) | **The fold and the floor**: wrapping is a fold over the structure tree — interior nodes administrative (paths/prefixes; opaque treatments short-circuit), leaves apply **codec references** (dictionary references: after typechecking, typeclass dictionaries are ordinary named defs, so `.bo`-resident descriptions reference marshalling code through the def namespace — in-body typed references resolved by instance resolution at the declaration, serialized by the existing def machinery; requirements per critique: qualified name, specialization identity, content hashes, a rooting rule so DCE cannot strip them, round-trip law hooks; coherence NOT assumed — hashes identify dictionaries when they become specialization keys, per §4.3). The fold bottoms at the **native floor**: the evaluator's built-in boundary vocabulary — concretely the `IConInfo` constructor list (`ICClock/ICReset/ICInout/ICMethod/ICStateVar/ICVerilog`) — the things needing no dictionary. The floor is the irreducible compiler (§5's dissolution succeeds exactly insofar as user-type-to-floor is spanned by dictionaries); **rendering targets are choices of floor** (Bluesim's C++ ABI is a second target today; typed-SystemVerilog ports raise the floor so structs stop flattening; zero-width is the floor's empty member). Consumer side is the same fold reversed — the **selection algebra** `interpret : FieldInfo × τ ⇀ (ICStateVar → τ)` (pure / applied / event / indexed / environment selection), partial exactly on spannability, deliberately non-unique in τ (multiple typed views of one boundary = the mediation freedom). BVI import = the reverse fold from hand-declared FieldInfos; round-trip laws of the leaf codecs are the soundness seam; wrap and unwrap are one decomposition read from the two sides (provider `to`-direction, consumer `from`-direction), so "feature 1 = feature 2" is structural. Corollary: **module wrappers are description-driven, not type-driven** — the same interface type legitimately renders many ways, so a type-indexed typeclass cannot generate wrappers (coherence = one instance per type; #714's "how to carry field pragmas" was this wall); renderings must never fork nominal types (no `ValidAction` — rendering is a property of a *place*, types classify *values*; the type changes iff the structure changes). `wrap(type, conventions/directives)` closes GenWrap (declaration directives), BVI (complete directives), and conformance (compare against declared) as one function used three ways | §5, §3.6, §12 |
| A99 | design discussion (2026-07-04) | **Compile-to**: bsc is asymmetric — it *imports* any boundary (BVI) but *exports* only the classic point; the missing export direction is the product (compile an implementation *to* a published description = ABI-stable vendor boundaries). The factoring theorem localizes each convention arm to wrapper-level wire algebra: provider-side ReadyValidRetractable = today's compilation plus one AND (`fire = valid ∧ RDY` at the WILL_FIRE join, `mkIfcWFs`), consumer side unchanged (classic EN = φ ∧ RDY drives a valid input soundly — implies ready, handshake completes immediately, persistence vacuous); Ack = plus one echo wire; consumer-side raw-willingness emission is a later optimization. Replication is the honest exception: the wrapper stamps ports but capacity is implemented by module internals, enforced by the member-compile check — emission renders, checking keeps it honest. First arm: ReadyValidRetractable, whose demo (a plain-BSV module presenting a valid/ready stream to a hand-written Verilog master that asserts valid during ¬ready) kills the always_ready/always_enabled wire-dump idiom; per A91 it must not be called AXI without the Irrevocable variant + skid | §3.6, §12 |
| A100 | design discussion (2026-07-04) | **Sealing soundness (from external critique; leak confirmed at code level)**: the phase-3 imposition copied the root member's *self-pairs* into the imposed schedule from all five relation lists and passed `sEXT` through — member accidents visible to the parent, breakable by substitution (root Action self-CF, alternate self-C: parent double-schedules, ifdef selects the alternate). The rule: **after sealing, no inferred member fact is parent-visible unless declaration-derived**. Self-relations get declaration-side defaults keyed by the structure's kind slots (read from `signature_<Ifc>_` via the def env): kind=value → self-CF (effect-free reads; guarded like the RDY fold against the root's own schedule), kind=action/actionvalue → self-C (single-use until capacity clauses, A95, exist), `RDY_*` faces → self-CF; `sP` self-pairs dropped; nonempty `sEXT` rejects group formation (conservative, rare). **Pinout equality is a mechanism precondition, not contract checking**: verbatim-ifdef instantiation requires identical port shapes, so the group site compares root-vs-alternate `VModInfo` pinouts (args by wire, per-method port shapes with `max 1` mult normalization, non-method fields — the era-1 fragments, minus the schedule/path refinement that stays dead) using the alternate `VModInfo` already in hand; a normalized pinout record enters the manifest as the seed of the future *surface fingerprint*. Groups stay semantically checkless; the vocabulary shift (imposition → **sealing**) makes leaks read as wrong: sealing that lets accidents through is visibly not sealing | §3.6, §12 |
| A101 | design discussion (2026-07-04) | **Naming ledger** (policy: name only what ships; pin nothing else). Pinned by shipping: **contract** / **clause**; **method convention** (the calling-convention family, user-endorsed and independently proposed by external review) with convention names `ClassicEnable` (default, never written) and `ReadyValidRetractable` (later `ReadyValidIrrevocable`, `RequestAck` — Chisel's Decoupled/Irrevocable as precedent); **fire** for the event facet (CAN_FIRE/WILL_FIRE precedent), facet triple *request/offer/fire*; **observes(observer, observed)** for dependence clauses; **wiring** = the realized total assignment; **sealing** as the internal verb for contract imposition. Recorded as open candidates, deliberately unhardened (code keeps neutral/transitional names; `signature_` def name is transitional, a one-string rename): structural stratum *shape* vs *schema* vs keep *signature* (external review argues signature imports ML-matching connotations and shape is more direct; *mapping* rejected for this stratum — a binder, not a translator); realization stratum *presentation* vs *rendering* (review: rendering sounds like pretty-printing) with *realization* as the process; published artifact *surface* vs *boundary* (review: surface stabilizes, boundary is the place; fingerprint = surface fingerprint); *facet* over *aspect* (avoids AOP echo); groups as *implementation family*/*variant group* in prose (never "checkless" user-facing). Rejected with reasons: ABI (software-colored), style/spelling/format ladder (superseded by convention), ValidAction-style type forking (A98) | §3.1.1, §12 |

---

## 10. Migration sequence

Ordered wedges; each is independently shippable, testable against the
previous compiler's output, and reversible. Rewrite-in-place of a 2299-line
load-bearing string-driven phase is how compilers die; every step below
leaves the tree releasable.

**W0. Hygiene and prerequisites (small, immediate)**
  - Typed Verilog parameter emission incl. signedness and the zero-width
    parameter guard (§7.1; closes #378, #550). Content-stable output flags
    (§7.3). Atomic-publish for bdir writes (§4.5).
  - Fix the known `alwaysEnabled`/`inhigh` propagation bug
    (`GenWrap.hs:1455`) — v1's `chkFieldBoundary` comparison is the test.
  - Replace the #658 port-sharing ICE with a positioned error (full support
    comes with W4's contract).

**W1. Upstream the v1 fallback feature (§2)** — parser, `vFallback ::
   Maybe Id` on `VModInfo`, `BoundaryTarget` targeting via existing pragmas +
   `IfcBetterInfo` overrides, post-schedule checks, Verilog `ifdef` swap,
   Bluesim link resolution, `.fallbacks` sidecar, `-require-fallback`.
   Carries its own 42-test suite. Byte-identical default output is the
   regression gate. **W1 is a family — the mkOneOf v0 ladder (§3.6, A25)**,
   each rung shippable atop the last: (a) v1 upstream as-is; (b) N-ary
   named fallbacks (`vFallbacks :: [(String, FEntry)]`, ifdef/elsif
   chains, `-use-impl`, sidecar → manifest v0 per A6); (c) external
   `` `define ``-anchor entries (`FEntry` carries the kind from the
   start); (d) the type-indexed `contractOf` primitive + BSV
   impl-selection groups (also delivering §3.4 pinning nearly free);
   (e) `fallback stub;` — the first derived Impl, stub generated as
   CSyntax from the group contract at GenWrap time (precedent:
   `genFuncWrap`, `bsc.hs:377-379`), making every BVI design
   Bluesim-able with zero user code and every synthesized module
   stubbable.

**W2. Declared-schedule attribute + regression pinning (§3.3-3.4)** — port
   `chkSchedRefinement` to source-declared and `.ba`-sourced contracts. No
   new machinery; highest issue-closure-per-line in the plan (enables
   closing #547-class documentation drift; the verify staging must honor
   A13/#631 from the start).

**W3. Fallback-only arguments (§2)** — value-generic vendor IP with one
   parameterized fallback; requires W0's typed parameters.

**W4. Contract object introduced (§3.1-3.2)** — subsume `wi_boundary_target`;
   `deffun`-fill and `chkBoundaryTarget`-verify become one function's two
   modes; contract-construction validation (closes #364's ICE class, #282's
   Classic asymmetry); `VFieldInfo` multi-output + port-sharing
   representation (A10/#339, A14/#658) ride the same `.ba` format bump.
   Otherwise internal; golden `.v` unchanged.

**W5. Flattening moves post-typecheck (§5, first wedge)** — the
   semi-separable `IfcTRec`/`genTDef` path runs on normalized types. This
   alone fixes the type-function-interface failure class (#313, #383).
   GenWrap's remaining pre-typecheck role shrinks to marking + `WrapField`
   constraint emission. Prerequisite: harden the synonym/type-function
   normalizer (#311, #325) — the new pipeline must not inherit its holes.

**W6. Enriched `Rep`/`Meta` (§5.1)** — independently useful (SplitPorts
   instances stop needing name plumbing; SV-type emission and external
   derivation unblocked). Library-side; compiler ships the derivation.

**W7. Flattening as a generic program; `wrapModule` injection (§5.2-5.3)** —
   delete `flattenFInfs`, `RDY_` mangling, `IfcTRec` minting (keep the thin
   nominal alias for `.bo` compatibility); boundary errors move to one
   constraint site. `IfcBetterInfo` deleted; elaboration naming reads the
   contract. Closes the string-namespace and minted-tycon bug classes
   (#307, #424, #234, #679, #820, #420, #617); error-quality bar set by the
   #729 fallout (#899, #900).

**W8. Specialization-first synthesis, rung 1 (§4)** — `ICPolySynth`,
   evaluator-computed keys (type vector + dictionary hashes), nested memoized
   `genModule`, `bdir` cache (with A7/A8 discipline), specialization
   manifest (A6), mangled-name ABI. Ships polymorphic `(* synthesize *)`
   per-point (closes #543, #358, #921; fixes #824). The wrapper is
   evaluator-instantiated `wrapModule` (needs W7; a W7-independent variant
   is possible but pays the per-key `runTI` cost).

**W9. Compression rungs 2-4 (§4.6) + mechanized zero-width variants (§6)** —
   content-hash dedup first (free), then the fragment checker (measurement),
   then shared front-end, then parameterized netlists with nonzero
   witnesses + derived `_z*` specializations. Each rung gated by the
   diff-match oracle against rung 1.

**W10. Monad-indexed boundaries (§5.5)** — `SynthBoundary`, delete
   `fixupPolyModType`; `ModuleContext`/`ModuleCollect` instances.

**W11. Interface-argument contracts (§3.5)** — research-shaped; after W2's
   contracts are proven at module boundaries.

Dependencies: W1→W3; W4→W7; W5,W6→W7→W8→W9; W7→W10. W2 is independent of
everything except W0 and can land first.

---

## 11. Risks and open questions

- **Solver cost and error quality at scale (§5.4).** The one-application
  injection concentrates typechecking into instance resolution; pathological
  interfaces (hundreds of methods, deep nesting) need measurement. Mitigation
  is in the wedge order: W5-W7 each have a bail-out, and the nominal-alias
  residue keeps `.bo` compatibility decoupled.
- **`.bo`/`.ba` format churn.** W1, W4, W8 each bump formats; the fallback
  work established the bump discipline (tagged signatures, hard version
  errors). Cross-version `bdir` sharing is out of scope by policy.
- **Schedule-refinement ergonomics (W2).** Partial declarations must be
  allowed (declare only the pairs you care about), or the feature is unusable
  on large interfaces; refinement semantics (declared ⊇ inferred conflicts,
  self-pairs excluded) is settled from v1, but the *surface* syntax for
  partial matrices needs a proposal.
- **Bluesim runtime-width vs stamped specialization (§4.6 rung 3-4).** Both
  exist in miniature (`WideData` vs per-width primitives); which the link
  step prefers is a performance question to measure, behind the manifest
  boundary of §7.2 either way.
- **Per-key scheduling cost.** Per-key specialization multiplies scheduling
  work, and scheduling is already superlinear on method-heavy conflict-free
  interfaces (#219). Rung 2 dedup and rung 3 shared front-ends are the
  designed relief; if they lag, family contracts verified by refinement
  (cheaper than re-inference) are the interim pressure valve.
- **The "backends read only `avi_vmi`" claim needs an audit.** #323 shows
  Bluesim's top-level harness keys on the literal `CLK` string, hanging when
  the boundary clock is renamed. Any such stringly backdoor must be found
  and fixed before contract-driven naming can be trusted end to end.
- **Fragment coverage.** The width-generic fragment's real-world coverage of
  the base library is unknown until the checker (first prototype step of
  W9) runs; rungs 1-2 do not depend on the answer.
- **Higher-rank types: a lever, not a dependency.** The A23 rank-1
  discharges stand for everything through W8. But HRT would pay in three
  endgame places: (i) a *first-class* `Impl` — user-written
  package-transforming combinators (`retimed`, `withAssertions`) must bind
  the existential, i.e. rank-2 elimination; without it every new combinator
  is an evaluator-blessed form rather than library code; (ii) direct relief
  on the #901 risk — polymorphic function arguments (rank-2 folds over
  `w`'s leaves) delete the instance gymnastics that typeclass-recursion
  encodings force on the solver; (iii) `runST`-style regioning for §5.5
  context handles. The gap is exactly **one pass wide: source
  typechecking**. Everything downstream of `IConv` speaks full System F
  today — ISyntax carries `ILam`/`ILAM` (`ISyntax.hs:455-458`, "vanishes
  after IExpand"), `ITCheck` *validates* F-typed terms, and the evaluator
  eliminates them; production is the only rank-limited stage. (The A23
  staging discharge is this asymmetry exploited: compiler-emitted code can
  be rank-2 already — "Prelude-typed but evaluator-meant" smuggles rank-2
  semantics past a rank-1 front end. Source-level HRT would not extend the
  compiler's semantics; it exposes to users what the internals already do,
  with the elimination side pre-verified by production use.) On the
  front end, schemes already segregate quantified variables (`TGen`,
  `Scheme.hs:17-45`) and the rigid/skolem concept exists in embryo where
  instance matching needed it ("Bound -- a rigid/skolem type variable;
  cannot be unified away", `PredTrie.hs:101,126,151`); what's missing is
  the discipline applied systematically through the *checking* path
  (THIH's infer-then-compare `tiExpl` corner) — the standard bidirectional
  rank-n recipe. Since the rigid/bound work lives in the same code W5-W7
  renovate, the hygiene should ride those wedges. Costs: explicit nested foralls in `CType`/`Type`
  (representation ripple through `Subst`/`GenSign`/`.bo`), predicative-only
  instantiation, and provisos under inner foralls (CtxRed learns to
  abstract constraints, not just float them — the subtle part). Staging:
  the rigid/bound hygiene is worth doing early regardless of rank (same
  species of cleanup as the GenWrap `qualEq` sins, and it keeps the rank-n
  door cheap); the extension itself earns its keep after W6/W7, when the
  generic-program experience quantifies how many instances it deletes.

---

## 12. As built: the A49 MVP implementation (increments 1–6)

Implemented on this branch, on top of upstream master, in six verified
increments (each demonstrated by compile *and* simulation, positive and
negative cases; every claim below has a test behind it). Total compiler
+ library diff ≈ 900 lines. All surface names are provisional.

**What exists.**

- `mkOneOf_ :: (Synthesizable a) => List (String, Module a) ->
  IfcContract -> Module a -> Module a` — run-and-decorate exactly per
  A40: the root instantiates normally, the just-created instance's
  `VModInfo` gains `vImpls :: [(String, VName)]`, and both selection
  surfaces exist: the Verilog backend emits an N-ary
  `` `ifdef``/`` `elsif`` chain (per-instance `BSV_IMPL_<inst>_<key>`
  first, then module-wide `BSV_IMPL_<rootVName>_<key>`, else the
  default), and Bluesim link takes `-use-impl name=key` with the same
  two-level name resolution, substituted once where the `.ba`
  hierarchy is assembled. Every module with selection points also
  emits a machine-readable manifest (`<mod>.impls.json`) naming each
  instance, its default, the alternates by key, and the exact macros
  and link flags that select them. `.ba` files are written by default
  for all codegen backends now (`-no-elab` restores the old
  behavior), so plain `-verilog` flows carry boundaries and manifests.

- `IfcContract` (MVP carrier: `(method, relation, method)` triples over
  CF/SB/SBR/C; unlisted pairs are conflicting; self-pairs outside the
  language, per the handoff) with `primImposeContract`: the declared
  freedoms are checked against the root's inferred schedule over the
  permission lattice (perms(CF)={par,ab,ba} ⊇ perms(SB) ⊇ perms(SBR)
  ⊇ perms(C)=∅; ME grants nothing pairwise), then the instance's
  recorded schedule is *replaced* by the contract — the parent
  schedules against the contract, not the member's accidents.
  `contractOf` and `wireMappingOf` read both descriptions off a
  boundary; `synthesize_` returns the `(interface, contract, mapping)`
  triple — acquisition by construction, per A42/A49.

- Alternate conformance (the soundness core): alternates are `Module a`
  values (interface equality from the typechecker), never run — a
  syntactic walk over the expression graph finds the one `ICVerilog`
  their post-synthesis wrapper (or BVI import) carries, and its
  `VModInfo` is checked against the boundary recorded on the root
  instance: identical instantiation arguments and method port shapes
  compared *by wire*, schedule refinement (the alternate must grant
  every recorded freedom; self-pairs excluded), path refinement (no
  new input→output combinational paths), and matching non-method
  fields. The gap case — permissive stub root, contract declaring
  `incr CF value`, register-based alternate granting only
  `value SB incr` — is rejected at compile time with the relation
  named.

- The typed layer, mirroring the existing wrapper machinery level for
  level: `SynthPort` (= anything in `Bits` — see finding 2),
  `SynthMethod` (instance heads mirroring `WrapMethod`'s),
  `SynthField` (adds Clock/Reset/Inout, mirroring `WrapField`),
  `Synthesizable` via the derived `Generic` representation
  (auto-derived for interfaces; the traversal is pure instance
  resolution), and `class (Synthesizable b) => WrapInterface a b`
  with *generic* instance bodies: `genericWrapIfc`/`genericUnwrapIfc`
  traverse the paired `Rep`s, pair fields by type-level name, and
  convert through `MediateField` (finding 3). `mkOneOf` and
  `synthesizeIfc` (`synthesize` is a Classic reserved word) are
  `unwrap ∘ core ∘ wrap`. The A46 layered errors work verbatim: a
  non-primitive field fails as an unresolved proviso chain naming the
  offending type (`SynthMethod#(...)` → … → `Bits#(Sub, _)`).

**What the implementation taught the design.**

1. *A47 is half-done upstream.* `WrapField name f w` / `WrapMethod m
   w` already exist in the Prelude — GenWrap's generated wrappers
   call `toWrapField`/`fromWrapField`; the per-field conversion is
   already class-directed library code. GenWrap's remaining
   irreducible job is inventing the nominal wrapper interface type
   and the instantiation plumbing. (§5.2's W6 is smaller than
   estimated.)

2. *`Synthesizable` must be the evaluator's proxy, literally.* The
   first cut accepted only `Bit n` ports and wrongly rejected
   `Maybe#(Bit#(8))`; upstream's own value-method instance is
   `(Bits a n) => WrapMethod a (Bit n)` — anything in `Bits` is a
   port. `SynthPort` now says exactly that; a `Maybe#(Bit#(8))`
   method is a 9-wire port and a subinterface fails at the missing
   `Bits` instance. Discipline: every typed-layer class mirrors an
   evaluator-machinery class or it will drift.

3. *Mediation is not a boundary crossing.* Routing generic interface
   conversion through `toWrapField` ICEs the evaluator: it wraps
   methods in `primMethod` port-name decoration (`ICMethod`) that
   only the synthesis boundary machinery can consume — applying a
   decorated method in ordinary code kills `conAp'`. Hence
   `MediateField`: instance heads mirror `WrapField`'s (methods
   through the shared boundary type, Clock/Reset identity, Inout
   through `Inout_ n`) but attach no decoration. Corollary for A28:
   the interpreter over field descriptions must distinguish the
   convert-only reading from the decorate-for-boundary reading.

4. *BVI drops out, as predicted (feature 1 = feature 2).* A BVI
   import carries the same `ICVerilog` as a post-synthesis wrapper
   with a declared `VModInfo`; the walk, `contractOf`, and all
   checks apply unchanged. Two representation accidents had to be
   normalized, both in the comparator, neither in the BVI path:
   logical clock/reset names differ (declared boundaries name them
   freely; compare by *wire*), and declared ready methods carry
   `vf_mult 0` where computed ones carry 1 (both mean one set of
   ports; normalize `max 1`, reject only true multiport mismatch).
   Demonstrated: a hand-written Verilog down-counter joins a group by
   BVI import, checks against the contract, and is selected in
   simulation; a BVI declaring `value C incr` against a contract
   promising `value SB incr` is rejected.

5. *RDY methods are literally boundary methods.* The boundary's
   conflict relation lists `RDY_x` as first-class value methods (both
   for computed and declared boundaries) — A48's "readys reify at b"
   is how `VModInfo` already models it. Cost: contracts for
   non-always-ready roots must declare RDY pairs explicitly. The
   contract language wants RDY folding (each method's ready absorbed
   into its own entry) — deliberately not built yet (finding 8).

6. *The canonical `WrapInterface` is a type-level function.* With
   generic mediation, canonical instances carry zero term-level
   content — two delegation lines; the fundep pair `(a, b)` is the
   instance. The irreducible residue is *naming* `b`: the boundary
   structure is computable (the `WrapMethod` fundep determines every
   field's `w`; mapping over `Rep a` gives the whole rep) but no
   library mechanism can birth the nominal type — which is exactly
   GenWrap's remaining job (finding 1). Endgame sharpened: expose
   the wrapper type GenWrap computes as a nameable type function
   (`Wrapped#(a)`, resolved at typecheck like `Rep`), and canonical
   instances vanish — `synthesizeIfc :: Module a -> …` with
   `b = Wrapped#(a)` internal. `WrapInterface` remains a real class
   only for deliberate re-wirings (credit protocols, SplitPorts-style
   splitting), with tag-newtypes on `a` for multiplicity — the
   existing `ShallowSplit`/`DeepSplit` idiom.

7. *Semantics choices now load-bearing (revisit deliberately):*
   group members share the parent's single instantiation, so an
   alternate's own module arguments in the group list are read for
   the boundary and otherwise ignored (`mkOneOf_` with
   `mkAdderStub(2)` against root `mkAdderA(1)` silently uses bias 1)
   — either document loudly or compare parameter expressions;
   imposition keeps the root's `rulesBetweenMethods` and `vPath`
   (checked for alternates, not declarable); an empty contract
   imposes nothing (root's inferred schedule is the implicit
   contract).

8. *Deliberately not built:* RDY folding (finding 5); declarable
   paths/rules-between; wire-map *imposition* (port renaming — now
   understood as a re-render under a declared spec, A36, and gated on
   finding 3's convert/decorate split); abstract
   `IfcContract`/`WireMapping` types with printers (transparent
   triple lists today); `Wrapped#(a)` (finding 6 — the recommended
   next compiler step); deep multiport (`vf_mult ≥ 2` untested).
   Breadth verified without code changes: members carrying Verilog
   parameters — including parameters *sourced from the parent's own
   parameters*, which stay symbolic through the swap (every branch of
   the chain instantiates `#(.bias(topBias))`, so a synthesis-time
   override of the parent feeds whichever implementation the macros
   select) — extra clock arguments, and extra reset arguments (the
   swap re-targets the module name and reuses the instantiation
   verbatim), an argument-list-narrower alternate rejected;
   cross-package groups; BVI members. *Port arguments are deliberately
   rejected at group formation*: a port argument is an interface
   argument in degenerate form (A1's used-interface contracts are its
   proper home) — what an implementation may assume about such an
   input (stability, read timing, clocking of the read) is not
   expressible in the current contract language, and `vPath`
   refinement covers only its combinational consequences, so groups
   over such boundaries would be checked incompletely; they error
   with the reason named. Consistent with A33's direction (module
   arguments shrink toward parameters). Deep multiport
   (`vf_mult ≥ 2`) remains the one untested argument-side dimension.

**A60 mechanics — the existential encoding, for reference.** The
per-entry relationship of `Boundary a`, in GHC notation:

```haskell
data BoundaryEntry a =
  forall name f w .
    ( HasField name a f        -- fact 1: `a` really has field `name`, of type `f`
    , WrapField name f w )     -- fact 2: that type wraps to boundary type `w`
  => MkEntry (Proxy name) Direction EntryFacts
```

Introduction is enforcement: the constructor demands both
dictionaries, so an entry describing a field `a` lacks is
unrepresentable; construction over `Rep a` discharges the constraints
per field (instance resolution is the existential introduction).
Elimination is capability without exposure: matching brings `f`/`w`
into scope abstractly with their dictionaries, so
`toWrapField p … (getField p ifc)` typechecks because both
dictionaries were packed mentioning the *same* hidden `f` — the
assembler can extract-and-convert any entry with no possibility of
converting one field as another.  GADTs would add only index
refinement, which no match here performs.  The pure encoding breaks
at the `.ba` (dictionaries cannot serialize; witness names rehydrate
by re-resolving instances and re-introduce the existential) and at
bsc's feature floor (no existential constructors, no rank-2 CPS) —
where the third elimination form applies: use sites are generic
traversals with the field statically in view, so evidence is
*re-proved* by instance resolution instead of carried
(`MediateField`'s pattern).

---

## 13. As built: the clean-slate declaration-first implementation (phases 0–3)

Executed on a fresh branch from upstream `main` (`534241d`), per A83's
reordering: the description substrate and declared contracts *first*,
groups as a nearly-free consequence. The §12 branch remains untouched
as the port source; everything below is either new code or a verbatim
port of its verified, on-path halves.

**Phase 1 — signature defs.** GenWrap emits one literal `CDefn` per
synthesized interface — `signature_<Ifc> :: List (String, List (String,
String))` — entries keyed by flattened field path, slots split by
stratum (A85): `kind`/`type` are signature, `prefix`/`argN`/`result`
are rendering directives (A86: slots stay inside BVI's committed
vocabulary). It lands in the `.bo` through the ordinary def pipeline
(no new Bin instances, per A61) and is readable by user code: a probe
module can `messageM` a formatted signature, and a library lint can
*reject* interfaces at compile time from their signature alone —
introspection as a deliverable, not a debug flag.

**Phase 2 — contracts declared at the interface, checked at each
member's own compile.** `contract_<Ifc>` beside the interface
declaration; `ContractCheck.hs` hooks `genModule` after scheduling,
where the inferred `VSchedInfo`, the interface type, the constant-RDY
set, and the full def map coexist. The check is actual-refines-declared
over the permission lattice (perms(CF) ⊇ perms(SB) ⊇ perms(SBR) ⊇
perms(C); ME grants nothing pairwise). Violations are rejected at the
*member's* compile with the relation named — the A78 inversion,
observed working. Per A87 the declaration surface is the typed carrier
from birth: Prelude `ContractStmt` constructors in a literal list, read
by a purely structural reader (a small head-normalizer resolves the
typechecker's dictionary lets; referenced defs are never unfolded, so
computation is rejected). There is no textual contract grammar
anywhere, and none should be added without substantial usage
experience. `RDY_*` names are rejected: readiness is the method's own
offer aspect (A82), spelled `contractAlwaysReady`.

**Phase 3 — selection groups, checkless.** The emission and selection
halves ported verbatim from §12 (they were always on-path): `vImpls`
on `VModInfo` with Bin instances and format bumps, the two-level
`BSV_IMPL_*` ifdef chain, Bluesim `-use-impl` link substitution, the
`<mod>.impls.json` manifest, `.ba`-by-default. The group surface
shrank to one primitive and one library line:

```bsv
Counter c <- mkOneOf(cons(tuple2("stub", mkCounterStub), nil), mkCounterA);
```

No contract argument — the group's contract IS the interface's
declared one, and an interface without a declared contract cannot form
a group (positioned error). `primMkGroup` does exactly two things:
*impose* the declaration on the root instance's recorded schedule
(declared pairs get their declared relation; unlisted pairs of
distinct methods become conflicting, so the parent schedules against
the declaration, never a member's accidents; self-pairs stay the
member's own — outside the language), and *record* the alternates'
Verilog names into `vImpls`. The §12 conformance machinery
(`checkAlternate`, the group-site walk-and-compare) does not exist
here at all: members were checked at their own compiles.

*Readiness folding at imposition:* `RDY_*` faces cannot be declared,
so the imposition folds them — every pair involving a `RDY_*` face is
imposed CF, guarded by a check that the member's own schedule grants
it (bsc-generated boundaries always do; the guard converts the
assumption into an error for exotic boundaries rather than trusting
it).

Demonstrated end to end: iverilog selects stub vs default by macro
(values 0 vs 2), Bluesim substitutes by `-use-impl` at link, manifests
list instance/default/alternates/macros/flags, groups form across
packages (the qualified `contract_<Ifc>` lookup), and the negatives
are positioned errors: no declared contract, non-synthesized
alternate, non-synthesized (inlined) root, port-argument boundaries
(A74: contracts on duals not yet expressible — rejected, not
half-checked).

**Residuals, recorded not hidden.** (1) Alternates' module-argument
and port shapes are not compared at the group site — the canonical
rendering makes same-interface members identical, but a member with
extra module arguments would produce malformed Verilog; the signature
def is the natural future carrier for this check. (2) Alternates'
`RDY_*` scheduling beyond the CF guard on the root is unchecked
(members' own compiles don't see RDY relations; benign for
bsc-generated members). (3) BVI members don't yet get the member-side
contract check (the §12 finding that BVI = declared boundary still
applies; it re-enters as a small import-validation check). (4)
`contractAlwaysEnabled` is recorded, not yet enforced against callers.

### As built, continued: increments A–F (post-critique, A88–A101)

Executed after the external critique of the architecture brief, in the
revised order (soundness before new protocol work).

**B — sealing soundness (A100).** The confirmed self-pair leak is
closed: sealing no longer copies any member self-relations or `sEXT`.
Self-relations are declaration-derived from the signature def's kind
slots, read through the def env with the same qualified-lookup pattern
as contracts (pragma-variant flattened names accepted by prefix):
value methods seal to self-CF (guarded against the member's own
schedule, like the readiness fold), action/actionvalue to self-C
(until capacity clauses exist); nonempty `sEXT` rejects group
formation. Pinout equality joins the group site as a *mechanism
precondition* (verbatim-ifdef instantiation), comparing each
alternate's `VModInfo` (already located, previously discarded) to the
root's by wire — module args, per-method port shapes with the
`max 1` mult normalization, non-method fields — and the manifest
gains a normalized pinout record (the surface-fingerprint seed).
Residual (1) above is thereby closed at the group site; the
member-compile form awaits declared port directives.

**C — `contractAlwaysEnabled` enforced (A90).** Sealing stamps a new
`VPmusthigh` port property (not `VPinhigh`: the instantiation must
keep classic members' EN ports connected — `VPinhigh` EN ports are
omitted from the port list), which keys the existing
`ProveEq use aTrue` obligation and raises G0015 at the *parent's*
compile (promotable to an error), exactly bsc's native
always-enabled semantics. Sealing requires `contractAlwaysReady` for
the same method (always_enabled implies always_ready) and rejects the
clause on value methods. v0 scope: the proof discharges when members
collapse their RDY wire (`always_ready` pragma); the sealed-constant
readiness fold at the parent awaits the conventions work. Residual
(4) above is closed.

**D — declared method conventions (A96).**
`convention_<Ifc> :: List#(ConventionStmt)` with one v0 statement,
`conventionReadyValid`, ClassicEnable the unwritten default. Read at
each member's compile, validated (unknown method, value method, and
`always_enabled` combinations are positioned errors), and stamped as
the new `VPreadyvalid` prop on enable ports through the wrapper
generator's port-props channel (merged per-name — `fixupPort` takes
the first entry per port). Conformance across a group holds by
construction (every member is stamped from one declaration).

**E — ReadyValidRetractable export (A91/A99).** The factoring theorem
as one AND: `aAddScheduleDefs` gates tagged methods' enable
expressions with their own RDY def, so the boundary accepts a request
asserted during not-ready, legally and without effect — fire =
request ∧ ready. Consumer side untouched (classic callers' EN already
implies ready); Bluesim compiles the same gated package. Demonstrated
against a hand-written Verilog master driving garbage requests during
not-ready: the state holds — the boundary that previously required
the `always_ready`/`always_enabled` wire-dump idiom is now a checked,
contract-carrying method. Retractable, not AXI (Irrevocable + skid on
the horizon).

**F — dotted-path atoms (A97).** Contract and convention atoms accept
`sub.method`, validated against the one admitted grammar
(`MethodPath ::= ident ("." ident)*`) and flattened at every
resolution site; sealing's kind lookup bridges the other way (the
signature def's paths are dotted — `fieldPathName` renders hierarchy
with dots; boundary names are the underscore rendering). The
group-site inline-root protection recognizes flattened subtrees.
Vector-index paths (`[_]` placeholders) remain future work with
aggregate clauses.

**G — BVI member-side checks (A90/A98).** "Feature 1 = feature 2"
completed for contracts: an `import "BVI"` is a hand-declared
boundary, so the actual-refines-declared check runs at the importing
package's own compile, reading the declared `VModInfo` in place of an
inferred schedule. The pass sits beside the post-`fixupDefs`
integrity check, where the current package's `ICVerilog` defs are
exactly the BVI imports and the full def map (including imported
contract defs) first coexists with them. Readiness is judged on
declarations: a method without a `ready` clause has no `RDY_<m>`
field (constant readiness, satisfying `contractAlwaysReady`); a
declared ready port is readiness NOT promised constant, and is
rejected against the clause. A BVI claiming a convention-tagged
interface is rejected (v0 — a BVI-side convention annotation lifts
this later). Declared boundaries remain trusted about their own
wires; the check is declaration-vs-contract consistency, never
declaration-vs-Verilog. Verified: a conforming ready-less BVI joins a
mixed group with an always_ready generated member and simulates under
both selections; a BVI whose schedule doesn't grant a declared CF is
rejected with the clause named.

**H — `-suggest-contract` (A25's migration aid).** Module generation
under the flag prints a paste-able `contract_<Ifc>` literal derived
from the inferred schedule: the declarable freedoms (CF/SB/SBR — ME/P
pairs are omitted, read back by the contract as conflicting) plus
constant-readiness facts, `RDY_*` faces folded. Suggestion is
extract-then-freeze: pasting the output beside the interface and
recompiling checks clean by construction. Printed at generation time
(so `-u` skips it when artifacts are up to date, deliberately).

Remaining residuals after A–H: alternates' RDY relations beyond the
root guard; the parent-side sealed-constant readiness fold; port-name
directives and the full declared-rendering equality check;
BVI-declared conventions; vector/aggregate paths.

### As built, continued: the dissolution round (increments 0–…)

**0 — suites into the repository.** The behavioral suites verifying
everything above, previously session-resident and lost with it, are
reconstructed from this section's record as native DejaGnu
directories under `testsuite/bsc.boundary/` (`p3`, `incB`–`incH`),
auto-discovered by `make check`. All expectations are frozen from
live runs (242 passes at the reconstructing commit); two spec items
are recorded as not currently constructible — a nonempty-`sEXT`
group rejection (the BSV parser's schedule completion does not
accept `EXT` self-pairs; the doubly-annotated pair ICEs
`mkVModInfo` before the group machinery runs — a pre-existing
parser bug, kept as a commented block in `incB.exp`) and Bluesim
selection of a raw-Verilog BVI alternate (`substAlternates` loads
alternates by `.ba` name; exercised under iverilog instead). The
compiler is untouched by this increment.

**1 — hygiene: the signature-variant scan is marker-gated.** Group
formation's fallback scan for pragma-variant signature defs
(`signature_<Ifc>_` absent, `signature_<Ifc>_AR_…` emitted by an
`always_ready` member's package) accepted any def whose name merely
extended the interface's — an unrelated interface named `Pulse_AB`
(alphabetically before the `AR` variant) was read as a variant of
`Pulse`, and sealing then blamed the contract with "method has no
entry in the interface's signature def" (reproduced live). The scan
now requires the extension to begin with a rename marker
(`AR_`/`AE_`/`EWR_`, exactly `ifcIdRename`'s vocabulary). Residual:
underscore-mangling ambiguity (a user interface literally named
`Pulse_AR_x`) remains until names stop being strings. Two other
planned hygiene items dissolved on inspection: the BVI fixup-time
check already keys on `isUserImport` structurally (not pipeline
phase), and the `GenWrap.hs` `alwaysEnabled`/`inhigh` XXX could not
be reproduced at the boundary surface (module-pragma and
interface-pragma `always_enabled` both drop the EN port identically);
it is left alone rather than guess-fixed.

**2 — `.ba`-by-default reconciled with the upstream suite.** The first
full upstream-testsuite run (increment 0's baseline: 18238 passes,
348 unexpected failures) exposed that phase 3's `.ba`-by-default
violated the byte-identical-default-output gate in two ways, both
previously unseen because the old session ran only the behavioral
suites. (i) ~268 golden diffs: every codegen compile now printed
"Elaborated module file created". The message is now gated on the
`.ba` being what the flags asked for — the Bluesim backend or an
explicit `-elab` (new `genABinExplicit` flag field; `-elab` under
Verilog keeps its message, per `bsc.driver/depend`'s golden) — while
the default-on write that carries boundaries and manifests stays
silent. (ii) Worse than cosmetic: a `.ba` written under the Verilog
backend satisfied `-u`'s Bluesim freshness check by timestamp, so a
verilog-then-sim sequence in one directory skipped Bluesim codegen
entirely — G0058-class checks (dynamic arguments, MCD/Inout
primitives) never ran, negatives flipped to passes, and Bluesim links
consumed `.ba`s lacking Bluesim-specific processing (parameter
inlining), crashing at runtime ("child process exited abnormally", 20+
suite failures). The artifact-level fact "which backend's processing
was applied" was never recorded distinctly: link-time checks compare
`apkg_backend`, which is `Nothing` for backend-neutral designs and
therefore matches everything. The written-backend is now read from
the already-serialized `abmi_flags` at the `-u` freshness check: under
the Bluesim backend, a timestamp-fresh module `.ba` counts only if
written by a Bluesim compile (decode failures, including older format
tags, count as stale). `.ba` header tag bumped
(`bsc-ba-20260706-1`, the `Flags` record grew a field). Residual,
recorded: link-time consumers still accept a wrong-processing `.ba`
if handed one directly — the same written-backend check belongs in
`decodeABin`'s compatibility test; deferred with the note that the
Depend fix removes every path the suite exercises. Verified: the
full-suite gate rerun passes 18564 with 26 unexpected failures, all
environmental (SystemC headers not installed; permission-denied
negatives that cannot fire as root), at 2:07 wall against the 2:13
baseline — the freshness decode is free at suite scale.

**3 — the typed layer, re-ported (project step 1).** The era-1 MVP's
library half lands in the Prelude: `SynthPort` (anything in `Bits`),
`SynthMethod`/`SynthField` (instance heads mirroring
`WrapMethod`/`WrapField`, plus Clock/Reset/Inout), `Synthesizable`
via the derived `Generic` representation, `MediateField`
(WrapMethod-mediated field conversion with no port-name decoration —
the era-1 ICE finding holds), `WrapIfc'` over paired representations
(leaves pair by `MetaField` name), and
`genericWrapIfc`/`genericUnwrapIfc`. Deliberately not ported:
`IfcContract` triples, `primImposeContract`/`primContractOf`,
`WireMapping`, `synthesize_`/`synthesizeIfc`, `primSetAlternates`,
and era-1's contract-argument `mkOneOf` — all superseded by the
declaration-first substrate; `WrapInterface` returns later as the
`wrapModule` constraint, designed against descriptions. Verified by
the new `bsc.boundary/typed` suite (25 tests: round trips on both
backends with writes landing through converted views, mixed shapes,
proviso negatives naming the offending leaf, `synthShape`
introspection), all nine behavioral suites green (271), and a
100-file golden-Verilog corpus comparison against the increment-0
snapshot: byte-identical — the layer is codegen-inert.

**4 — the de-closure (the increment-I precondition).** GenWrap's
wrapper continuation (`DefFun`, a closure over the GenWrap-time monad
state and pragma snapshot, invoked by `genModule` after scheduling)
becomes `GenBoundary.renderWrapperCDefn`: `mkDef` now returns a pure
`BoundarySpec` (wrapper def id/type, ifc-declaration pragmas as
per-type facts, module pragmas as data, the state snapshot), and the
module-pragma input is an explicit parameter chosen at the call site.
`bsc.hs` currently passes the same GenWrap-time set — verified
byte-identical against the full 542-file golden corpus (zero diffs),
271 boundary-suite passes, 2353 passes across the naming/codegen/MCD
matrix. The staleness that ICEd the original increment-I attempt is
now structurally reachable: the RDY filter, `fixupVeriField`, and the
readiness guards all read the parameter, so `genModule` can hand them
the same pragma set the scheduler sees. Type-level naming
(`flatTypeId`) deliberately stays on the GenWrap-time snapshot — the
flat type's identity must not change when post-typecheck pragmas
arrive (renderings never fork nominal types, A98).

**5 — increment I ships: `contractAlwaysReady` collapses the RDY
port.** `genModule` computes the module's effective pragma set once
at entry — GenWrap's set plus what the interface's declared contract
implies (`ContractCheck.contractReadyPragmas`; dotted paths flatten
to the boundary rendering) — and that one set drives elaboration,
scheduling, the always-ready proof (`ENotAlwaysReady`/G0006 at the
member's own compile when readiness is not provably constant), the
boundary field filter, the wrapper's readiness guards, and the
recorded `.ba` pragmas, so the schedule and the recorded boundary
agree by construction. Two seams surfaced and closed during
verification, each instructive: (i) the wrapper renderer briefly kept
receiving the GenWrap-time snapshot while the schedule used the
effective set — `mkVModInfo`'s pair-completeness check refused the
desync, the mirror image of the failure that motivated the round,
caught by the same guard; (ii) the flat nominal type keeps its RDY
field (type identity is a GenWrap-time fact) while the collapsed
import lacks it, so the `CmoduleVerilog` completeness check learned
that a missing `RDY_<m>` for a declared method reads as constant
readiness — the semantics ready-less BVI declarations always had.
`.ba` tag bumped (recorded pragmas now include the contract-derived
set). Verified: `bsc.boundary/incI` (25 tests — the collapse is
clause-scoped: declared methods lose `RDY_*`, an undeclared guarded
method keeps its port; a separately-compiled parent consumes the
collapsed boundary through the `.bo` on both backends; the guarded
negative raises G0006; the increment-G mixed group re-forms with NO
`always_ready` pragma anywhere, the pragma-free generated root's
pinout equal to the ready-less BVI's); all ten behavioral suites
green; corpus comparison shows zero diffs outside contract-carrying
tests, and every contract-carrying diff is exactly the RDY-port
removal (port list, declaration, wire, constant assign). This
closes the §13 "parent-side sealed-constant readiness fold" residual
for generated members: parents see constant readiness as ordinary
evaluated truth.

**6 — boundary descriptions with codec references, proven by shadow.**
GenWrap emits `boundary_<flatifc>` beside `signature_`: a literal
`List BoundaryEntry` whose field entries carry the leaf's flattened
path and rendering slots and — because `primMkFieldEntry`'s
`WrapField` proviso is resolved by the typechecker at the declaration
against the leaf's name and type proxies — a reference to the leaf's
codec dictionary, serialized through the ordinary def machinery
(A98/A61: the reference is a def-graph edge, not a name string; the
`f`-typed proxy argument keeps the proviso unambiguous).
Clock/reset/inout leaves are opaque entries (the native floor needs
no dictionary); foreign interfaces are excluded. `BoundaryDesc.hs`
reads descriptions back post-typecheck (readers shared with
ContractCheck; `CodecRef` holds the resolved dictionary reference),
and the hidden `-check-wrap-shadow` flag compares the described
boundary against the assembled one at every module generation.
Description defs are rooted (`DefP_Boundary`); `.bo`/`.ba` tags
bumped.

The proof is the discovery loop: the full suite ran under the flag
until the only failures were the known environmental set. Four
rounds, each teaching something real: (1) the checker's own lookup
misconstructed the def name from the already-suffixed flat id — and
en route exposed that flag-on suite compiles after flag-off twins
were `-u`-skipped no-ops (the increment-2 lesson recurring in test
form; the shadow suite now compiles against erased state). (2)
Vector positions are index-parametric in descriptions
(`subs.[_].put`, one shared codec — the upstream WrapField
index-erasure) but index-concrete at boundaries: the comparator
matches parametrically, and index-count completeness is explicitly
NOT description data until A97's aggregate clauses. (3) Clock and
reset leaves flatten like everything else; kind classification must
run on synonym-expanded types; output-port presence is not
description data (a zero-width result drops its port — the floor's
empty member). (4) Vector-of-clock fields match parametrically too,
and the `value` kind is the emission's catch-all — a type-function
method type (the #313/#383 hole) cannot be classified pre-typecheck,
so the fallback kind asserts nothing; only positively-identified
kinds assert their port shape. Convergence: the full suite under the
flag reports ZERO shadow disagreements (18606 passes; residual
failures are the known environmental set plus nine option-echo tests
that any injected TEST_BSC_OPTIONS perturbs by design). One
description side-effect surfaced and was fixed on the #900 precedent:
a boundary def re-proves the wrapper's WrapField provisos, so a
non-synthesizable interface errored twice at one position — the
package typecheck now reports a boundary description def's failures
only when nothing else failed (they are strictly derivative; the def
is still poisoned). Final state: the description substrate spans
every boundary the ~18.6k-test suite synthesizes, member-for-member,
with per-leaf codecs resolved and `.bo`-resident — the fold
increment's precondition.

**7 — the fold as producer (pilot).** Under the hidden
`-boundary-fold` flag, the wrapper's interface-rendering body is
built from the `boundary_` description's field entries
(`genFromBodyDesc`, a pure function) instead of re-walking the
symtab: the description supplies per-leaf structure and naming — the
path, kind, and prefix/result/arg slots replace the
interface-pragma recomputation — while method types still come from
the interface inventory (types are not description data yet) and
codec application remains the `fromWrapField` class application the
solver re-resolves to the very instance the description recorded.
The defensive posture is total: any disagreement between description
and inventory, an opaque leaf, or a hierarchical/vector path falls
back silently to the legacy walk, so a stale or out-of-scope
description can never change output. Verified: byte-identical
generated Verilog flag-on vs flag-off across a 233-file corpus (163
renders folded across 102 distinct modules; all 48 fallbacks are
subinterface/vector/clock/reset/inout shapes — the widening
worklist); all eleven behavioral suites pass in both modes; the
full suite under the flag shows only the known environmental and
injected-flag-noise failures, at the fastest wall time of the round
(1:38) — the fold is free. The round's residue for the next
increment set: widen the pilot (the fallback shapes), move method
types into descriptions, apply codecs by reference (the
ISyntax-direct renderer), then the §5.3 one-application injection.

**8 — the fold widened to every synthesized shape.**
`genFromBodyDesc` became a `GWMonad` recursion mirroring
`genFromBody`'s walk case for case — subinterface recursion, vector
expansion, opaque clock/reset/inout leaves — consuming description
entries in the DFS order the emission produced them (`boundaryEntries`
and the walk share the traversal discipline, so the orders agree by
construction; a vector position consumes one entry per concrete
index, the path index-erased to `[_]`). Structure and types still
follow the FInf inventory; the description supplies the naming
outright — the WrapField name proxy and the `saveFieldPortTypes`
prefix/result/argN values. At every leaf the flattened path
(`fieldPathName`), the kind (opaque vs method), and the declared
argument names must agree, and any disagreement — or leftover
entries — falls the whole module back to the legacy walk silently.
Opaque entries now carry the naming slots too (`primMkOpaqueEntry`
gained a slots argument; `.bo` tag `bsc-bo-20260708-1`): the legacy
walk emits `saveFieldPortTypes` for clock/reset/inout leaves as
well, so the fold needs their prefix/result values from the
description. Verified: the 233-file corpus renders 211 folds with
ZERO fallbacks (increment 7's 48-shape worklist retired: every
fallback was subinterface/vector/opaque, including the whole
AR-on-interface family, which fell back for its subinterfaces, not
its pragmas), byte-identical Verilog flag-on vs flag-off; the
thirteen boundary suites pass (340), including the new
`bsc.boundary/fold` suite (each widened shape asserts its `fold`
decision in a `BSC_BOUNDARY_FOLD_LOG` census, renamed/prefixed/
indexed port names checked in the generated Verilog, a Bluesim
testbench runs through folded wrappers); and the full suite under
`-boundary-fold -check-wrap-shadow` COMBINED — every module
generation folds and is shadow-compared — shows a failure set
byte-identical to the known environmental + option-echo set, at the
round's fastest wall time (1:35:18). One test-harness lesson: a
suite's `unset` of the census env var killed logging for every
suite after it in the one-process runtest run — save and restore.

**9 — method types verified from descriptions.** Each `boundary_`
field entry's resolved method type turns out to have been in every
`.bo` all along: the `f`-typed proxy argument (kept for proviso
disambiguation, A98) is `(CAny :: f)` at the declaration, which
iConv renders as `primBuildUndefined` applied AT the field's method
type — so the type is the application's type argument, recovered by
a type-keeping head walk (`headTypes`; `whead` discards type
arguments, which the first smoke run found immediately: every leaf
reported "no recorded type" and the fold correctly refused to fire).
No emission or format change. After a successful fold walk, every
leaf's recorded type is compared against `iConvT` of the interface
inventory's leaf type (the walk consumed the entries in order, so
they pair up positionally); a mismatch or unrecoverable type falls
the module back to the legacy walk silently and is a positioned
error under `-check-wrap-shadow`. From this increment on, a fold
that fires is a fold whose description types are PROVEN true — the
description is self-sufficient data: path, kind, naming, type, and
codec reference per leaf. Verified: corpus 211 folds / 0 fallbacks
byte-identical with verification live; boundary suites 345
(including a new cross-package pair — types recorded at the
declaring package's compile, verified at the member's); and the
full suite under `-boundary-fold -check-wrap-shadow` with an
unbroken census: **3781 folds, ZERO fallbacks across the entire
~18.6k-test run**, failure set byte-identical to the known
baseline, wall 1:36:15 — the verification is free. The residue for
increment 10: consume the recorded types and codec references in an
ISyntax-direct renderer, bypassing the per-module wrapper
re-typecheck (`compileCDefToIDef`'s one-def
ctxreduce/typecheck/simplify/iConv pipeline, `bsc.hs:2430-2457`,
which re-solves per module what the description already records).

**10 — codecs by reference, verified (re-scoped).** Planned as the
ISyntax-direct renderer; re-scoped when ground truth changed the
economics. Dumps of every wrapper shape at the `DFwrapper_*` stages
showed the final wrapper IDef is a fixed template (monad-bind spine
→ one `ICVerilog` → `saveFieldPortTypes` chain → interface
construction) whose inline `WrapField` dictionaries are exactly the
closed expressions the descriptions record — the renderer is fully
designed (template spec, typed-CSyntax-into-`iConvDef` shape, and
the constructor-encoding hazards are archived in this increment's
commit history and the session notes) — but the per-wrapper
pipeline it would bypass (`compileCDefToIDef`: a one-def
ctxreduce/typecheck/simplify/iConv per module, `bsc.hs:2430-2457`)
costs single-digit milliseconds, and the §5.3 relocation does not
need the bypass (that pipeline already runs post-typecheck inside
genModule and is reusable as-is). So the increment proves the
codecs instead: under `-check-wrap-shadow`, after each wrapper
compiles, every `fromWrapField` application in the compiled
definition is located, its let-bound dictionary inlined (wrapper
lets are applied-lambda shapes), and compared STRUCTURALLY against
the recorded `CodecRef` — recorded codecs made self-contained at
read time by inlining the description def's own lets. One real
finding, immediately: a noinline wrapper regenerated in an
importing package (b1356) re-solves its `TupleSize` proviso — an
EVIDENCE-ONLY class, numeric fundep evidence, no methods — to a
differently CONSTRUCTED but observationally identical dictionary
(structural `ICTuple` vs the source instance chain), so
evidence-only nodes compare by their fully-applied class type
(methodness judged from the symtab) while method-bearing
dictionaries stay strictly structural. Verified: corpus 211/0
byte-identical; fourteen suites; the full lane's failure set
byte-identical to baseline with censuses 3781 folds / 0 fallbacks
and 3704 dictionary comparisons across 3788 modules (a
non-vacuousness census hook, `BSC_CODEC_SHADOW_LOG`); the whole
shadow stack (boundary + types + codecs) costs ~8% on a
wrapper-heavy slice, less at suite scale, in the diagnostic lane
only. With naming (8), types (9), and codecs (10) all proven, the
description fully determines the wrapper's semantic content: the
ISyntax renderer is now an optimization, not a prerequisite — the
§5.3 injection (increment 11) proceeds on the mini-pipeline.

**11 — the §5.3 injection relocation, piloted.** Under hidden
`-boundary-inject`, the wrapper skeleton stops being package
content: it is not typechecked into the parent-visible environment
beyond its stub, it is absent from the `.bo`, and it is compiled at
`genModule` time by the same per-module `compileCDefToIDef`
pipeline that has always compiled the final wrapper. (The opening
bid — don't plant the skeleton at all, assemble it from the
recorded `BoundarySpec` with the user's def left unrenamed and
unstubbed — did not survive contact; the rounds below are the
story of WHY, and the recording infrastructure it built —
`bs_vtis`/`bs_argpts`/`bs_moddef` on `BoundarySpec`, the shared
`convModArg`/`mkArgCtx`/`collectIfcInfoW` — stays as increment
11b's seed.) Seven discovery rounds fixed the architecture, each a
real finding. (1) A genModule-built skeleton's
cross-package references carry iConv's placeholder bodies —
undefined-value stubs that elaborate into `∀`-typed ICE — so a
captured definition must be re-knotted against real definitions
(the hunt instrumented `PrimTypeOf`/`PrimPrintType`/`evalCExpr`
with recursive `ITForAll` guards, kept as permanent diagnostics).
(2)+(3) One def cannot be both parent-facing (polymorphic
`∀ m c. IsModule` — importers typecheck against it) and
Module-forcing (the skeleton body needs `m := Module`): tying it
forces T0029 "too general" locally or G0013 mismatches in parents —
the legacy stub/body SPLIT is load-bearing and stays. (4) The
skeleton cannot skip the package pipeline either: typecheck of the
planted skeleton is what renders user errors in module argument
types (T0043 with position, vs positionless T0031 later) and what
marks imports used (spurious T0157 otherwise). (5) It cannot skip
`iSimplify` — but iSimplify deep-forces, so running it per-def
after re-knotting materializes the transitively-inlined import
graph (256MB heap exhaustion), and running it before fixup inlines
the placeholder bodies away. (6) The whole-package `fixUp`
re-stamps positions, clobbering inner error positions (EBigLit3's
T0051 moved). (7) The re-knot must refresh EVERY same-package
reference, not just the generated members: two generated modules in
one package, the second instantiating the first, reach the sibling
only through the renamed user def — a non-generated package def
whose capture-time embedded body still carries the pre-synthesis
knot — and elaborating the parent against that stale knot spun the
evaluator forever (bsc.scheduler's IgnoreRdy; it was also the
silent killer of the early full-lane attempts, which sat in the
spin until the session's container was recycled). Completeness of
the widened set is structural: any path from the skeleton's spine
to a stale reference passes through a first `ICon`; a package def's
replaced body is globally current, and an import cannot reference
this package at all. The settled shape follows from those
constraints:
the skeleton is PLANTED at GenWrap exactly as today and rides the
entire package pipeline — typecheck, iConv, fixupDefs, iSimplify —
then its finished IDef is CAPTURED and the def DROPPED from the
package before the generation loop, so the `.bo` carries no
skeleton (verified by dumpbo); at its module's genModule turn the
captured IDef is re-knotted SELECTIVELY (`fixupIDefSel`: only
same-package generated-member `ICDef` bodies, from the
already-updDef'd current package, no position rewriting) and handed
to the existing wrapper pipeline. Net: the wrapper definition is no
longer package content — not typechecked into the parent-visible
environment beyond its stub, not in the `.bo`, constructed
per-generation — which is the §5.3 relocation's pilot invariant,
with the pre-typecheck ADDITIVE half (flat types, codecs,
descriptions, the stub) still planted and scheduled to move in the
derived-flat-types increment (11b). Verified: corpus 233 files
byte-identical flag-on vs flag-off (IgnoreRdy's own schedule dump
included); fifteen boundary suites pass both modes (370) including
the new `bsc.boundary/inject` suite (census `inject`-per-module
with zero `legacy`, prefixed-subifc and param/port/vector-arg
boundary names, the same-package sibling regression, a moved-phase
user error that keeps its message and tag, composition with
`-boundary-fold -check-wrap-shadow`, Bluesim behavior); and the
full ~18.6k-test suite under ALL THREE flags — every module
generation injected, folded, and shadow-compared — shows a failure
set byte-identical to the known baseline, with censuses (
accumulated across the lane's salvage reruns; the invariants are
exact): 4867 injected generations / ZERO legacy, 4163 folds / ZERO
fallbacks, 3925 codec dictionary comparisons. Residue: the
ISyntax-direct renderer (archived design) would drop the
per-generation `compileCDefToIDef`; increment 11b derives the flat
interface types instead of planting them (per-instantiation
minting, the flat type demoted to derived data + a temporary
compatibility key with an explicit consumer burn-down); then the
default flip.

---

## Appendix A. Codebase fact sheet (verified citations)

All verified against `main` @ `534241d`:

| Claim | Citation |
|---|---|
| GenWrap is 2299 lines, runs 5 phases before typecheck | `GenWrap.hs`; `bsc.hs:384` vs `bsc.hs:428` |
| Own synonym expansion / qualEq shadow type system | `GenWrap.hs:39-41`, `1851`, `1784` |
| Syntactic ifc derivation (`ifcNameFromMod`/`getArrows`) | `GenWrap.hs:638`, `641` |
| Flattening duplicated (GenWrap ×2, IExpandUtils, bluetcl, SymTab/parser) | `GenWrap.hs:708-710`, `IExpandUtils.hs:1514-1585`, `bluetcl.hs:1960+`, `SymTab.hs:392`, `CVParser.lhs:2988-3013` |
| Symtab staleness + rebuild | `GenWrap.hs:354-355`, `bsc.hs:387-391` |
| `alwaysEnabled` dropped/broken XXX | `GenWrap.hs:1455` |
| `IfcBetterInfo` "needs re-thinking" | `IfcBetterInfo.hs:33-34`; consumed `IExpand.hs:958-970` |
| `VModInfo` width-free | `VModInfo.hs:561-569`, `178-185`, `270-286` |
| Parent trusts declared submodule schedules | `ASchedule.hs:1710-1712`, `2779`, `4420`, comment `3875-3888` |
| `ICVerilog` con and instantiation | `ISyntax.hs:774-777`, `IExpand.hs:1377-1408`, `3188` |
| Nested elaboration precedent | `AAddSchedAssumps.hs:221-239` |
| `always_ready` declared-and-verified | `AAddScheduleDefs.hs:181-197`, `FlagsDecode.hs:1617-1619` |
| `genC`/`genVerilog` selectors + taint | `IExpand.hs:3910-3925`, `bsc.hs:476-489` |
| Bluesim rejects foreign imports | `ABinUtil.hs:279-285`, `Error.hs:3586-3591` |
| `WrapField` class + GenWrap constraint emission | `Prelude.bs:4619-4630`, `GenWrap.hs:907-921` |
| `WrapMethod` elaboration-time errors | `Prelude.bs:4663`, `4707`, `4718` |
| `SplitPorts` generic programs over `Meta`/`Conc` | `Prelude.bs:4781`, `SplitPorts.bs:32-85` |
| `MetaField` carries name+index only | `Prelude.bs:4607` |
| `primMethod` / `primSavePortType` | `Prelude.bs:4614`/`2593`, `IExpand.hs:3170`/`1410` |
| `Expose`/`Hide` context reification | `ModuleContext.bsv:86-91`, `135-136`, `234-264` |
| `fixupPolyModType` hard-substitutes `Module` | `GenWrap.hs:581-595` |
| Zero-width variants + dispatch + filtering | `src/Verilog/{FIFO10,SizedFIFO0,RWire0}.v`, `FIFOF_.bsv:111-138`, `AVerilogUtil.hs:1034-1037`, `SimPrimitiveModules.hs:72-73` |
| SPSRAM computed-name idiom | `SPSRAM.bs:73-79`, `45` |
| `RegFile.v` width-parameterized | `RegFile.v:23-26`; `RegFile.bs:52` |
| Bluesim runtime-width C++ | `bs_wide_data.h:16-82` (`WideData`) |
| OVL params: enums packed, counts `Int#(32)`, widths `SizeOf`-based | `OVLAssertions.bsv:57-107`, `743-752`, `2450-2463` |
| Fork symbols absent upstream | tree-wide: no `vFallback`/`BoundaryTarget`/`chkSchedRefinement`/`wi_boundary_target` |

---

## Appendix B. b2r: typed waveform decoding via viewer translator plugins

*Assessment (2026-07-03) of cross-generating Rust equivalents of Bluespec
types plus Rust decoders derived from the actual `Bits` instances, targeting
waveform-viewer translator plugins (e.g. Surfer's). Surfer comes out of the
Spade project, whose native typed decoding through this interface is the
existence proof of the UX; verifying the current state of Surfer's plugin
API is step zero.*

**The trick, stated as staging.** "Partially apply the known `unpack` to an
unknown bit vector" is two-level partial evaluation: static = the type
instantiation and the resolved `Bits` dictionary; dynamic = the bits.
Specialize away everything static — inline the dictionary methods, unfold
the generics `from`/`to` conversions (they vanish at concrete types),
unroll `Vector` recursion (bounded by known widths) — and the residual is
first-order functional code over the dynamic bits: extract/concat on
slices, tag-compare if-chains, constructor applications. That residual
translates near syntax-directedly to Rust, with the b2r type mirror
supplying the target `enum`/`struct` definitions.

**The load-bearing decision: translate the post-typecheck *functional*
ISyntax, not the elaborated hardware.** At the hardware level, `unpack`
followed by the boundary's implicit `pack` is near-identity and the names
are gone; the post-typecheck ISyntax retains constructor-level structure
(`ICCon`/`ICIs`/`ICOut`/`ICSel`/`ICTuple`, `ISyntax.hs:759-772`), which is
what the Rust translation needs. The stuck-on-dynamic staging is the same
discipline as §4.6's fragment check, except stuck means *residualize*
rather than error; `genFuncWrap`/noinline (`bsc.hs:377-379`) is the
existing synthesize-a-pure-function precedent, and `AAddSchedAssumps`
remains the run-the-machinery-standalone precedent.

**The relationship to this design is structural, not thematic.** The
decoder's identity is (definition, type vector, dictionary-tree hash) —
*the same key as §4.2*. A Surfer decoder for `T` is a demanded
specialization artifact of the pure function `unpack`, memoizable in the
same cache, listable in the same A6 manifest; and the dictionary hash
answers the question waveform decoding otherwise gets silently wrong:
*which* `unpack` did this signal use (§4.3, bsc#731). The type mirror is
§5.1 consumer 6; the signal→type table is consumer 5, served by the
recorded `BoundaryBinding` mapping (§3.1.1).

**Tiers, sized honestly:**

1. **Derived `Bits` only, metadata-driven — weeks.** Layout is a pure
   function of the type definition; generate Rust types and decoders
   directly from type metadata (same shape as consumer-3 SV emission; also
   subsumes #395). Wants to be a bsc/bluetcl emission mode — `.bo` parsing
   outside bsc is version-locked pain. Note: once SV packed-type ports
   (A16) exist, simulators record typed values on the SV path and Tier 1
   is subsumed there; Tier 1 still pays for VCD-from-Bluesim and non-SV
   flows.
2. **Custom `Bits` via partial evaluation + ISyntax→Rust — months (2-4 for
   one person who knows the evaluator).** (a) a curated partial evaluator
   over the pure ISyntax fragment with bounded unfolding — where the effort
   concentrates, and a strict subset of what W8 needs (same
   demand/key/memo skeleton, no scheduling, no backends: building it first
   de-risks W8; building W8 first makes it nearly free); (b) the
   residual-to-Rust translator — small, the fragment is small; (c) fallback
   policy: instances escaping the fragment (foreign calls, unbounded
   recursion) degrade to raw-bits display.
3. **Beyond boundary ports — gated on the naming story, then cheap.**
   Ports already have recorded name→type associations (`primSavePortType`);
   internal signals collide with generated-name instability (#401) and wait
   on the naming consolidation. Once selection-path names are stable
   (§5.1/A18), interior coverage needs no per-signal type table: a signal
   whose stable name is a selection path rooted at something typed (a
   boundary port via the binding's surface-type field, a register of known
   type) gets its type *inferred* by walking the path through the Rep — the
   viewer resolves interior signals with the same metadata it uses at
   ports. Scope v1 to boundary ports and method args/results regardless.

---

Corrections applied relative to earlier drafts of the design discussion: the
`alwaysEnabled` XXX is at `GenWrap.hs:1455` (not ~1521); the
symtab-staleness admission is at `GenWrap.hs:354-355` (386 is a different
XXX); `getSimModName` exists only on the fallback branch (upstream's closest
symbol is `vNameToTask`, `AVerilogUtil.hs:1103`); `backendMatches` lives in
`Backend.hs:27-30`; `WrapField`'s fundep is `name f -> w` (the name proxy
participates); `reburyContext` belongs to `Hide`, not `Expose`; the
computed-name idiom uses `integerToString`, not `itos`; Bluesim's
runtime-width type is `WideData`, not `tUWide`; OVL numeric parameters are
`Int#(32)`, not `Bit#(32)`.
