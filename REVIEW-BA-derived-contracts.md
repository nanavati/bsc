# Review: "Exact BA-Derived Module Contracts Using Bluespec Generics" (v0.1, 2026-08-21)

**Reviewed against:** B-Lang-org/bsc `main` @ `941eecf` (the commit the proposal cites); the
2026-08-21 Open-source Bluespec sync notes/transcript (including the cited 00:39:30–01:28:04
range); and standing org design-policy decisions (PL-literature review requirement of
2026-08-15; the CtxRed-removal audit; in-flight `.bo`/`.ba` format-tag work).

**Method:** six independent adversarial review lenses (typeclass/Generic semantics; evaluator
and fixup mechanics; BA sufficiency; artifacts/digests/build graph; migration/compatibility;
document quality), each finding then independently adversarially verified against the source
tree; two supportive passes (code-grounded strengths; meeting/org alignment); and a
completeness critic over the whole review. Every claim below carries `file:line` evidence that
was checked twice (once by the finder, once by a verifier instructed to refute it). Where the
finder and verifier disagreed on severity, the disagreement is stated and resolved explicitly.

---

## Verdict

The proposal is an unusually well-researched design document: its account of current BSC
behavior is accurate down to closure parameter lists and maintainer XXX comments, its scoping
discipline (exact identity before compatibility, explicit non-goals, one named blocker) is
exactly right for a stress-test target, and it faithfully serves both the 2026-08-21 meeting's
decisions and the org's CtxRed-audit direction. Its central empirical claim — that the BA plus
the symbol table covers what the inverse wrapper consumes — **largely survives its own audit**:
of the eight DefFun inputs, six are BA-present or symtab-derivable, and the two that are stored
nowhere (`veriPortProps`, `true_ifc_ids`) are the two the proposal itself pre-named in §7.3.

It is not implementable as written. The review found:

1. **One unspecified load-bearing mechanism** — the design never says how boundary types and
   Generic/Wrap* evidence get *constructed* after the canonical BO exists, and the machinery it
   plans to "extract from GenWrap" does not live in GenWrap: it is spread across GenWrap,
   Deriving, package-wide CtxRed, and the typechecker.
2. **An unsound migration sequence** — Phase 3 (canonical BO) deletes the only cross-package
   carrier of opacity before Phase 4/5 provide its replacement, making the plan's own testsuite
   exit criterion unsatisfiable as sequenced.
3. **A set of concrete falsifications** of specific §5–§9 claims, each with a counterexample
   in the current source: `abmi_oqt` is not the source-visible type; internal rule names sit in
   the boundary schedule data; the flattening stopping rule as stated diverges from
   `genIfcField` on testsuite-covered inputs; `noinline` redaction happens pre-typecheck and is
   function-shaped; Bluesim has no per-module backend object; the canonical digest is a deep
   normalization project, not a serializer variant.

None of these refute the architecture. Nearly all have resolutions inside the proposal's own
framework ("add the datum", "make the decision explicit", "re-sequence"), which is itself
evidence the design is sound at the core. But three of them (items 1, 2, and the pragma-semantics
question F-A7 below) must be resolved in the document before implementation starts, not
discovered mid-prototype.

Raised: 42 adversarial findings + 6 completeness gaps. After adversarial verification:
**2 critical, 12 major, the rest minor/question** (several majors were downgraded from the
finders' initial severities; two verifier downgrades were themselves overturned on review —
noted inline).

---

## Part I — Adversarial review

### Critical

#### F-A1. The evidence-construction engine does not exist and is not designed *(merged: types-lens TC-1 [CONFIRMED critical] + evaluator-lens F1 [WEAKENED major]; tiebreak below)*

**What the proposal claims.** §4.1 step 2 / §6.1: at provider-elaboration time, after loading
the canonical BO, "derive the boundary module type and resolve the existing Generic, WrapField,
WrapMethod, SplitPorts, and WrapPorts evidence." §13 Phase 1: "Extract one reusable
boundary-shape derivation from GenWrap."

**What the code says.** The boundary type is not computed by GenWrap alone, and no resolver
exists outside the CSyntax frontend:

- GenWrap emits flattened-interface struct fields whose types are a **free type variable under
  a WrapField constraint** — `cf_type = CQType [CPred (CTypeclass idWrapField) [...]] v`
  (`GenWrap.hs:907-921`). The concrete boundary field types are *outputs* of fundep
  improvement, solved later by **package-wide context reduction** over struct fields
  (`CtxRed.hs:62-70, 86-88`, invoked from `bsc.hs:412`).
- Dictionaries are inserted only by the CSyntax typechecker (`bsc.hs:428`;
  `TypeCheck.hs:35-46, 142-151`); supporting auto-derived instances come from Deriving
  (`bsc.hs:396-398`; `Deriving.hs:957-993`); conversion to ISyntax happens in `iConvPackage`
  (`bsc.hs:463`). The symbol table is rebuilt twice precisely because GenWrap and Deriving add
  types and instances (`bsc.hs:387-419`).
- There is no ISyntax-level instance resolver anywhere. The only single-definition entry
  points — `cCtxReduceDef` (`CtxRed.hs:49-57`, used by GenWrap itself at `GenWrap.hs:538`) and
  `compileCDefToIDef` (`bsc.hs:2192-2219`) — are CSyntax typechecks, and `compileCDefToIDef`
  cannot add new types/instances to the symbol table, which boundary derivation requires.

**Why it matters.** In the new model the canonical BO — by the proposal's own §1.1 goal —
contains none of the generated boundary types, `to_`/`from_` conversion defs, or resolved
evidence. Producing them post-BO-load therefore requires either (a) a mini-frontend re-entry at
provider-BA time (generate a CSyntax slice, rebuild a symtab from `.bo` signatures, run
Deriving + CtxRed + typecheck + iConv on it) — i.e., a *generated-source typecheck relocated to
the provider side*, in tension with §3.5's framing though compatible with every consumer-facing
goal — or (b) a new evidence-construction engine outside the TI monad. Neither is designed.
§14's "Boundary evidence representation" and "Target type storage" rows cover only how to
**store** evidence, not how to **construct** it; §13's Phase 1–2 estimates omit the bulk of the
actual work. This also lands squarely on the org's CtxRed-audit finding that GenWrap today
depends on the package-wide cleanup pass — there is no self-contained derivation to extract.

**Tiebreak on severity.** The two lenses' verifiers split (critical vs major). The mitigating
facts are real: the pieces of horn (a) all exist (`mkSymTab` already rebuilds symtabs from
imported signatures on every compile; Deriving, `cCtxReduceIO`, `cTypeCheck`, `iConvDef` are
all callable), so this is missing *orchestration and a design decision*, not missing
technology. But the mechanism in question is the single load-bearing element of the entire
design; the document neither chooses a horn nor prices one; and choosing horn (a) contradicts
the document's own §3.5 rhetoric, while choosing horn (b) is a subsystem the phases never
mention. A design review must rate an unspecified core mechanism as blocking: **critical**,
with the explicit note that a viable resolution shape is known.

**Remedy.** Add a design section that states which compile first materializes the boundary
shape, from which instance environment, using which machinery. Either (1) specify the
provider-side mini-frontend re-entry (symtab from `.bo` signatures + generated slice +
per-slice CtxRed/typecheck/iConv), acknowledge that a generated-source typecheck survives on
the provider side, and cost it; or (2) make the CtxRed-audit refactor (GenWrap computes one
concrete boundary description without the global cleanup pass) an explicit Phase 0.5
prerequisite, and specify the on-demand constraint-resolution API. Either way, close the loop
with the org's CtxRed-removal direction explicitly.

#### F-A2. Phase 3 deletes the only cross-package opacity carrier before its replacement exists *(compat MIG-1, CONFIRMED critical)*

**What the proposal claims.** §13 sequences: Phase 3 "Write a canonical full BO regardless of
generation selections"; Phase 4 external contract artifact; Phase 5 compatibility driver.
§13.1 requires "the full current testsuite produces equivalent parent BAs and backend results."

**What the code says.** Today opacity crosses package/invocation boundaries **only inside
`.bo` bytes**: the post-synthesis wrapper is substituted via `updDef` (`bsc.hs:620`) and the
mutated package written as the `.bo` (`bsc.hs:648-649`). Even within a single `bsc -u` run,
each depended package is compiled by a separate `compilePackage` that re-reads the child's
`.bo` from disk — the generated `.bo` is explicitly *not* added to the in-memory maps
(`bsc.hs:657-659` XXX comment; `compile_with_deps` at `bsc.hs:254-293`). Documented behavior:
`user_guide.tex:688-695`. Multi-invocation flows are the testsuite norm (e.g.
`testsuite/bsc.bluetcl/hierarchy/hierarchy.exp` runs two separate `bsc` invocations), and
Bluesim linking and bluetcl hierarchy browsing walk parent-`.ba` submodule instantiations
(`SimExpand.hs:69`, `ABinUtil.hs:127`, `bluetcl.hs:1040-1043`).

**Why it matters.** The binding overlay (§8.2) is an in-memory, per-elaboration structure. The
external contract that would carry opacity between invocations arrives only in Phase 4, and the
driver that would supply contracts automatically only in Phase 5. After Phase 3 alone, every
parent compiled in a different `compilePackage` call than its synthesized child — i.e., every
cross-package flow, including a single `bsc -u -verilog -g mkTop` — reads a canonical
full-source child `.bo` with **no input that selects opacity**. The parent silently inlines the
child: no Verilog module boundary, orphaned child `.v`, changed `.ba` hierarchy, broken bluetcl
and Bluesim-link flows. §13.1's own "minimum acceptable first landing" bundles Phases 2–4 but
still omits the Phase 5 driver while demanding full-testsuite parity — unsatisfiable, since the
testsuite drives `bsc -u` with no mechanism to supply contracts. **Critical for the plan as
sequenced.**

**Remedy.** Re-sequence or bridge: land contract emission plus driver-side automatic contract
threading (e.g., an on-disk `.ba`/contract read as an implicit contract for imported
synthesized modules) in the same phase that canonicalizes the BO — or have Phase 3 keep
emitting the redacted personality alongside the canonical BO until Phase 5. State in §13 which
phases must land atomically for §13.1 to be evaluable.

### Major

#### F-A3. `abmi_oqt` is not the source-visible module type; the §8.1/A.2 binding template mistypes every `IsModule`-polymorphic module *(evaluator F4, CONFIRMED)*

`getDef` synonym-expands the type and applies `fixupPolyModType`, which substitutes the
`IsModule` type variables with `Module` and **drops the proviso** (`GenWrap.hs:543-554,
581-593`); `writeABin` stores exactly that as `abmi_oqt` (`bsc.hs:963-967`; `ABin.hs:59-62`'s
own comment confirms the empty pred list). Today's inverse wrapper is deliberately declared at
the *other* type — the ctx-reduced polymorphic `cqt` — with a `liftModule` re-generalization
(`GenWrap.hs:1459-1460, 1527, 1532`). Consequently §6.2's equation "original source module
CQType = `abmi_oqt`" is false for every `IsModule`-polymorphic synthesized module (the BSV
default); A.2's `assert source type == contract.shape.sourceModuleType` fails against the
imported signature; and an opaque binding built at `abmi_oqt` cannot replace the polymorphic
canonical definition (needs ILAM binders, an `IsModule` dictionary lambda, and `liftModule` —
none present in the template). §14's "Target type storage" row is about the *boundary* type,
not this. **Remedy:** store the pre-`fixupPolyModType`, ctx-reduced declared type in the
boundary-shape record; specify the binding with compiler-generated type/dictionary abstraction
plus `liftModule`; define the A.2 check as equality after synonym expansion.

#### F-A4. `noinline` is a generated-module class the design cannot express, and its redaction happens pre-typecheck *(evaluator F5 + compat MIG-3, both CONFIRMED)*

`genFuncWrap`/`addFuncWrap` run **before typechecking** (`bsc.hs:375-394`), gated on the mere
presence of *any* backend flag, and replace the function's definition with
`fromWrapNoInline`-over-`Cforeign` (`GenFuncWrap.hs:230-273`) — so today's `.bo` for a package
with `noinline` functions already differs based on `backend flags /= Nothing`, independent of
`-g` **and of elaboration**. Two consequences: (a) the §3.3 narrative that personalities are
created by the post-elaboration continuation is incomplete — canonicalizing the BO requires
*not performing* a pre-typecheck source transformation the architecture sections never mention;
(b) the consumer-side binding for a `noinline` function is **function-typed and
ICForeign-backed** (`IExpand.hs:3287-3304`), which neither §8.1's module-typed
`primInstantiateBoundary` nor §5.2's module-shaped adapters can express. §12.2 has a
"No-inline functions" test row but no design; §14 has no row; Appendix B omits
`GenFuncWrap.hs`. **Remedy:** either scope `noinline` out of v1 in §2.4, or add a
function-shaped contract/primitive design and specify the canonical-BO representation
(original body retained, overlay selects).

#### F-A5. Internal rule names are boundary data today; §9.3 row 1 is falsified until the schedule projection strips them *(ba F4 CONFIRMED + artifacts F2 + spec DOC-2)*

`VSchedInfo`'s `rulesBetweenMethods`/`rulesBeforeMethods` carry the child's internal rule
names (`SchedInfo.hs:33-47`, with the maintainers' own XXX: "they don't exist on the
boundary"), are baked verbatim into the boundary `CmoduleVerilog` (`GenWrap.hs:1525`), and are
genuinely consumed by the parent scheduler and its diagnostics (`ASchedule.hs:4413-4427, 4745,
3322`; rule names surface in parent error messages). Rename an internal rule — a pure
implementation change — and the §7.1-defined schedule contract changes, the digest changes,
and every parent rebuilds: §9.3 row 1 ("internal child rule changes → no parent rebuild") is
false as written. §14's "minimal schedule projection" row flags the area, but the review's
verifier confirmed the framing itself is broken: a projection "without implementation detail"
cannot simultaneously satisfy §8.3's "exact same contract it sees today", invariant 8's
same-parent-BA (child `VSchedInfo` sits verbatim in parent BA bytes), and oracle-equal
diagnostics — while retaining names breaks row 1. **Remedy:** decide now — digest only method
pairs/direction; carry rule-id lists (if at all) as explicitly non-digested diagnostic fields;
add a "rename an internal rule" row to §12.3; give §7.4 a digested/undigested field split.

#### F-A6. The canonical digest is a deep normalization project; positions are load-bearing in identities *(artifacts F3, CONFIRMED)*

Every serialized `Id` carries its `Position` and `IdProps` (`BinData.hs:683-694`), positions
carry file-path FStrings (`:666-677`), the sharing machinery keys Ids on
base+qual+position+props (`:239`), and props embed positions and uniquification state
(`:718-730`). Worse, positions are baked into **name identity**: `enumId` embeds its numeric
argument in the name string (`Id.hs:332-336`) and GenWrap creates generated boundary-interface
type names from the *source line number* (`GenWrap.hs:742-743`, foreign/BVI path) — inserting a
blank line above a BVI import changes a boundary-facing type name. "Excluding positions" is
therefore not a serializer variant: it requires a distinct normalizer (alpha-renaming of
generated/bound ids, per-prop semantic-vs-diagnostic classification, sorted collections), which
is precisely GHC's multi-release interface-fingerprint determinism effort — budgeted here as
one sentence (§7.4). Invariant 7 and §12.3 test 4 depend on it. **Remedy:** scope the digest
normal form as its own workstream; add "insert a blank line above the module" and "rename a
let-bound helper" stress rows with pass condition "identical contract bytes"; engage the GHC
prior art.

#### F-A7. "Absence of a contract means source remains available" silently inverts `(* synthesize *)`/`(* noinline *)` semantics *(compat MIG-2, CONFIRMED)*

The documented, recommended way to request a boundary is the source attribute
(`user_guide.tex:465-468`); under `bsc -u`, depended packages get `genName = []`
(`bsc.hs:259-261`), so pragmas are the *only* selector in real recursive flows. In the new
model the boundary exists only if every parent build action passes the right contract, and
forgetting one produces **structurally different RTL that simulates identically** — silent,
netlist-inspection-only regression for hierarchical synthesis/PnR/ECO/keep-hierarchy flows.
§10.4 has no diagnostic row for "synthesize-marked module elaborated transparently"; §14 has no
pragma-vs-build-input row; §8.4 treats it purely as driver ergonomics. This is a language
semantics question: what does the pragma *mean* in the new model? **Remedy:** define it — at
minimum, transparent elaboration of a synthesize/noinline-marked module without an explicit
opt-out should be a diagnosable event in the core action; add the §10.4 row and a §14 decision
row.

#### F-A8. The compatibility driver must reconstruct on-disk personality semantics the proposal abolishes — and it is undesigned *(compat MIG-4, CONFIRMED)*

Today's semantics are a function of on-disk state left by earlier invocations
(`user_guide.tex:697-705`), and `-u` staleness is pure timestamps (`Depend.hs:185, 254-271`);
nothing records which generation choices produced an artifact. Making the `.bo`
generation-invariant removes the one signal `-u` uses. To reproduce current behavior the driver
must answer, per imported module, "was hardware generated for this, and against which
artifact?" — exactly the per-module record the canonical BO removes — and needs a new staleness
rule (parent stale when a child's *contract* changes though the child `.bo` is byte-identical).
Every candidate mechanism (scan for `.ba`/contracts and trust them; a generation database;
pragma re-derivation) has distinct silent-failure modes. The meeting itself said most BSV code
in the wild breaks without a legacy solution (notes, 01:22:56 area and the deferred-decision
row). §8.4 spends one paragraph; §14 — otherwise thorough — has no row. **Remedy:** add §14
rows for driver discovery + staleness; or scope legacy-driver semantics as a required
companion design that must land before Phase 3 flips BO semantics (ties to F-A2).

#### F-A9. `veriPortProps`: backend-derived port properties are structurally unavailable under the target phase split *(ba F2; verifier downgraded critical→major on grounds this review overturns in part)*

The DefFun receives `veriPortProps` only when the child is compiled with the Verilog backend
(`bsc.hs:953-961`, else `[]`); they are computed by `getIOProps` **nine lowering passes past**
the APackage stored in the BA (`bsc.hs:1104-1182`, `VIOProps.hs:57-61`) and are baked into the
parent-visible boundary `VFieldInfo` (`GenWrap.hs:1516-1517, 1637-1657`), then consumed
transitively by the *parent's own* `getIOProps` (`VIOProps.hs:148-172, 236-285`). The verifier
downgraded on the ground that the datum could be captured "at its computation point" into the
BA — but that escape exists only in today's single-pass pipeline; §2.1 explicitly assumes
"backend objects are generated separately" *after* the BA, where the datum does not yet exist
when BA and contract are produced. The genuine options are: embed the Verilog lowering subset
in contract projection (backend-entangled projection + a missing §9.2 edge), accept per-backend
contracts, or declare `VPconst`/`VPunused` non-semantic and accept documented parent-RTL deltas
versus the oracle. Note also: **the oracle itself is backend-dependent** — a `-sim` child gives
`ips=[]` today, so "reproduce the exact behavior of today's wrapper" is ill-posed until the
proposal picks which personality is the target. **Major** (a decision with a viable sanctioned-
deviation option, not an unresolvable blocker), but the decision must be made in §7, not
discovered in Phase 4.

#### F-A10. Evidence identity via "stable references and hashes" is unimplementable with existing infrastructure and unsound without transitive fingerprints *(types TC-3, CONFIRMED)*

BSC's only hashing facility is the whole-`.bo` hash computed at read time (`GenBin.hs:39-47`,
`BinData.hs:1543-1547`); no per-definition hash exists. §12.3's two bullets are **jointly
unsatisfiable by any non-transitive scheme**: bullet 1 (provider-private helper change must
NOT flip the contract) rules out package-granularity hashes for the provider package — where
the generated `Generic`/`to_`/`from_` defs always live — while bullet 2 (custom-instance
helper change MUST flip it) rules out per-def non-transitive hashes. Satisfying both requires
GHC-style transitive per-declaration fingerprints (undesigned, no prior-art engagement) or
embedding the full typed evidence closure — which strains §1's "small contract / no
implementation body" framing and reopens §14's instance-visibility question at full
generality. **Remedy:** commit v1 to embedding the typed evidence closure (the only option
implementable without new fingerprint infrastructure), quantify its size in Phase 0,
canonicalize positions in the embedded slice, and defer references+hashes until a fingerprint
scheme is designed against the GHC prior art.

#### F-A11. The stated flattening stopping rule diverges from `genIfcField` on supported, testsuite-covered inputs *(types TC-4, CONFIRMED)*

The real vector rule (`isVectorInterfaces` → `chkInterfaceVectorElementType`,
`GenWrap.hs:1755-1783`) recurses through nested `Vector` **and `ListN`** (`:1842-1850`) and
accepts elements that are **Clock, Reset, or Inout** — not just interfaces. Live testsuite:
`bsc.codegen/vector_interfaces/ClockVectorIfcGate.bsv` (`Vector#(n, Clock)` interface field).
Under §5.3 verbatim, `Vector#(3, Clock)` becomes one `WrapField` leaf whose default chain
requires `Bits` — a derivation-time error where today's compiler emits per-element clock
fields. Separately: `genIfcField` emits a compiler-generated `Bit#(1)` **RDY companion field**
per method leaf, pragma-gated (`mkReadyField`, `GenWrap.hs:926-947`) — a peer field of the
boundary struct produced by *compiler policy*, not by any WrapField resolution, undercutting
§2.3's "classes determine leaf policy" slogan; and interfaces containing polymorphic fields
fall to the leaf case (`isAnyPolyFieldType`, `:1691-1698`). There is also no `isInterfaceType`
function (§5.3 names one); the predicate is `chkInterface`. These are exactly the "supposedly
derivable boundary fact actually missing" counterexamples the proposal solicits — found
statically. **Remedy:** amend §3.4/§5.3 to the actual rule (recurse through Vector/ListN when
the ultimate element is interface/Clock/Reset/Inout); specify RDY-field synthesis as an
explicit compiler-side derivation step; add `Vector#(n,Clock)`/`ListN` and poly-field rows to
§12.2.

#### F-A12. "Without typechecking that wrapper a second time" really means "replaced by an unspecified type-equality and contract-validation judgment" *(spec DOC-4, CONFIRMED)*

Today the re-typecheck is the mechanism that *guarantees* the replacement definition has the
original type. The proposal deletes it and substitutes (a) A.2's two asserts, whose equality
judgment is undefined — `CQType` equality in BSC is derived structural `Eq`
(`CType.hs:298-299`), sensitive to proviso order, synonyms, and variable naming, while the
promised "normalized" form is defined nowhere — and (b) unchecked trust that the frozen
evidence inhabits the claimed adapter type. Cross-package, cross-compiler-run type comparison
plus evidence well-formedness checking is a real subsystem (Backpack's signature matching is
its literature shape); §13 has no line item, §14 no row, §10.4 no rows for malformed contracts
or stale evidence. **Remedy:** add the normalization/equality judgment as a design section or
§14 row; add contract-validation as a named Phase 4 deliverable; extend §10.4.

#### F-A13. Whether compiler/IR version feeds the digest is undefined — and it decides whether every release invalidates every cache *(spec DOC-3, WEAKENED to major and held there)*

§7.1 puts "compiler/IR version" in contract Identity; §7.4's digest input list omits it; A.1
has neither (only `derivationVersion`), and §7.1's "Provider assertion" row describes data
that lives in a different artifact. A consistent GHC-like reading exists (version gates
deserialization; digest covers semantics) — but the document never states it, §6.2 pulls the
other way ("correctly invalidated"), §4.4 makes digest equality the sole substitution gate,
and §14 has no digest-composition row. With three format-tag bumps in flight this week and
performance the org's top demand, this single unstated decision governs whether §9.3's "No
rebuild" rows survive a compiler release. **Remedy:** make one section normative; split
identity into a semantic digest and a format/compiler-version deserialization key; move the
provider assertion into the BA/link-plan artifact descriptions.

#### F-A14. No performance exit criterion, in a design justified by performance *(spec DOC-5, held at major)*

"Performance" and "rollback" appear nowhere in the proposal. §13.1's exit criteria are purely
behavioral: a first landing where contract load + validation + evidence deserialization at
every parent elaboration costs more than the eliminated wrapper typecheck would still be
declared a success — in an org whose #1 compiler demand is critical-path and total-CPU
performance. Phase 3 (fixup rewrite + BO semantics change for all users) precedes any contract
payoff with no flag or exit ramp (Phases 1–2 do keep the legacy path; nothing covers backing
out after Phase 3). **Remedy:** add a §13.1 performance criterion (parent-elaboration time
within X% of baseline; measured cache-hit win on the child-internal-change scenario); keep the
legacy replacement path behind a flag until Phase 5 parity is demonstrated.

#### F-A15. Zero prior-art engagement, against a standing org decision *(spec DOC-1 + artifacts F8, CONFIRMED)*

§B.2 lists exactly two sources: the meeting and the source tree. The org's 2026-08-15 decision
requires PL-literature review before designing language/compiler extensions; the meeting
itself invoked GHC's process as the model (transcript: "This would be similar to how GHC does
some of its big things"). Each missing citation corresponds to an open design question found
elsewhere in this review: GHC's interface-hash/ABI-hash/flag-hash split → F-A13; GHC
deterministic-uniques/fingerprint normalization → F-A6; GHC orphan tracking (BSC already warns
`WOrphanInst`, `GenSign.hs:406`) → §10.2/§14 instance visibility; Backpack signature matching
→ F-A12; OCaml `.cmi` digest cascades and diamond "inconsistent assumptions" errors → §10.4;
Rust per-item fingerprints → schedule projection; Build Systems à la Carte / content-addressed
builds → early cutoff and the store-vs-reproduce choice; Verilog stub flows and Liberty `.lib`
timing models → the semantic-vs-backend split. **Remedy:** a prior-art section mapping each
system to the § it informs — per the KB decision, a gate, not a nicety.

#### F-A16. Bluesim has no per-module backend object; §9.1/§9.3's backend rows are wrong for one of the two primary backends *(completeness-critic gap, verified in this review)*

§9.1 defines "Backend object: per-module Verilog, C++, or other backend output generated from
the BA." For Bluesim this does not match reality: link-time codegen consumes the **full
`ABinModInfo` of every module in the hierarchy** (`SimExpand.hs:61-75` — `simExpand` over all
`fabis`), builds a combined cross-module schedule (`combineSchedInfos`, `SimExpand.hs:736,
893`), and emits C++ from the whole `SimSystem` (`SimMakeCBlocks.hs:75-80`). A child
implementation-only change with an unchanged contract still changes the *entire* generated
simulation — so §9.3's backend-facing cache rows are untested and wrong-as-written for
Bluesim, and the elaboration-level cache win (which survives) must be distinguished from the
link-level one (which does not exist for Bluesim today). No §12.2 row covers this.
**Remedy:** split §9.1/§9.3 claims per backend; either scope Bluesim's backend object as
"whole-system, rebuilt on any child BA change" for v1 or add per-module Bluesim codegen as
future work.

#### F-A17. Dependency cutoff silently narrows for the common package layout, and `.bo` hash chaining defeats it independently *(evaluator F2 + artifacts F4, both WEAKENED but jointly major)*

`fixupDefs` merges all defs of all imported packages and internal-errors on any missing
reference (`FixupDefs.hs:33-38, 100-107`); `.bo` loading pulls the transitive closure
(`BinUtil.hs:95-99`); and each `.bo`'s `ipkg_depends` records the writer's entire loaded
closure as **content hashes** (`FixupDefs.hs:42`, `bsc.hs:529-531`, `GenBin.hs:44-46`). Two
consequences the document never states: (a) when a parent uses *anything* else from the
provider package (exported types, instances, helpers — the common layout), the provider's
canonical BO with its full closure is a parent input, so §12.3 test 3 holds only for parents
whose sole reference into the provider package is the contracted module; there is no artifact
between "whole canonical BO + closure" and "single-module contract". (b) Even in the clean
case, a private provider change alters the provider `.bo`'s content hash, which is recorded in
the parent's own `.bo` (`ipkg_depends`), changing the parent's bytes and cache key — the
rewritten fixup in A.3 drops `ipkg_sigs` recording without comment, and nothing says hash
chaining must be replaced by signature-identity recording. **Remedy:** state the limitation;
add per-definition slicing or an "evaluator-defs-without-module-bodies" projection as future
work; add the explicit design item replacing `ipkg_depends` content hashes with signature
digests; add a §12.3 test: change a provider-private helper, re-typecheck the parent, require
byte-identical parent BO.

### Additional findings from the completeness pass (verified)

- **F-A18. Poison-pill personalities.** On wrapper-generation failure with poison pills
  enabled, the BO is written with `mkPoisonedCDefn` substituted (`bsc.hs:588-592`) — a *third*
  BO personality (source / redacted / poisoned) with dedicated load-time semantics
  (`WPoisonedDefFile`/`EPoisonedDef`, `BinUtil.hs:178-200`, `IExpand.hs:776-778, 3512-3514`).
  The proposal's §3.3 taxonomy, canonical-BO invariant, and A.3 fixup never mention it, and
  §12.2's "Schedule failure" row covers contract non-emission only. Define what a
  partially-failed multi-module generation produces under the canonical-BO model; add a
  poison-pill row.
- **F-A19. Cross-contract evidence coherence (the diamond problem).** Nothing specifies what
  happens when one parent elaboration loads contract A (frozen against `CustomPorts` at digest
  X) and contract B (frozen at digest Y): two evidence graphs referencing the same qualified
  instance/type names at different digests must coexist in one ISyntax environment where type
  identity is by qualified name (`MakeSymTab.hs:544-553`) and `.bo` loading is whole-package
  by hash. §10.4 has no conflict diagnostic; §12.2/§12.3 have no mixed-contract test; A.1's
  `evidenceDependencies` has no merge semantics. This is OCaml's "inconsistent assumptions"
  error and GHC/Backpack ABI unification, concretely instantiated. Add the design decision and
  a two-contracts-divergent-evidence stress row.
- **F-A20. Instantiation-time diagnostic obligations.** Today's wrapper body is evaluated by
  the parent's iExpand, which produces positioned, user-facing errors at the instantiation
  site (module-argument extraction, param-only enforcement `IExpand.hs:867` +
  `IExpandUtils.hs:393-394`, clock/reset hookup checks, undetermined-argument diagnostics,
  poisoned-def errors). §8.3 specifies only method/schedule exposure; A.2 is error-free; §12.2
  has no error-parity row. Enumerate which evaluator errors `primInstantiateBoundary` must
  replicate, with position attribution, and add error-parity tests.

### Minor findings and questions (verified; compressed)

| # | Finding | Disposition |
|---|---|---|
| m1 | §5.2's module-argument story ("using SplitPorts and WrapPorts") is answerable from source and the answer is **no**: Clock/Reset have no `Bits`, params are String/Real (`isParamType`, `GenWrap.hs:1816-1820`), inouts use a dedicated cast, vectors are blasted with `_0/_1` names (`expandArg`, `:559-577`), and args deliberately do **not** see custom SplitPorts instances — routing them through SplitPorts would change the module-argument ABI. §14 flags the question; close it: keep bespoke per-argument adapter data (mirroring `ArgInfo`) and reserve SplitPorts/WrapPorts for method ports. Also: the adapter needs argument-side `Bits` dictionaries, which sit outside all five classes every prose enumeration of frozen evidence names. *(types TC-2 + evaluator F6, WEAKENED — answers an acknowledged open question)* |
| m2 | "Evidence reused unchanged" (§5.2/§11.1-3) is loose: today's wrapper is `from_` **specialized by post-elaboration facts** — `true_ifc_ids` guard elision (`GenWrap.hs:1577-1580` XXX comment, `:1625-1626`) and port-type/name recording. The consumer conversion is a function of types + evidence **+ contract data**; qualify the invariant as "evidence identity plus contract-directed specialization" and state where guard elision happens. *(types TC-5, WEAKENED — §7.3/§7.1/§14 pre-name the datum)* |
| m3 | `BoundaryIfc`'s fundep + name-based boundary-type identity is unsound: `flatTypeIdQual` drops type-argument qualifiers (`GenWrap.hs:1875-1892`), so distinct source types can collide on one boundary-type name. Make boundary-type identity in contracts structural/content-based; treat generated names as diagnostic labels. *(types TC-6, surviving core)* |
| m4 | §6.1's provider binding `Foo.mkM := toBoundaryModule(Foo.mkM.source)` rebinds the original name at a different type inside the fixup map — type-unsound for recursive/mfix references and undetected by `ISyntaxCheck` (`ISyntaxCheck.hs:185` trusts the reference annotation). Today's code deliberately uses a fresh id with the source def inlined (`modIdRename`, `GenWrap.hs:625, 1369, 1383`). Bind under a fresh internal name; also enumerate the non-def duties (pragma nub, `ipkg_sigs`, ATF cache) A.3's replacement must preserve. *(evaluator F7, CONFIRMED minor)* |
| m5 | `primInstantiateBoundary` must replay elaboration-time **effects**: `saveNameStmt` and argument port-type recording (`genFromBody`, `GenWrap.hs:1554-1572`; `mkArgPortTypes` `:1537-1549`) land in the parent's `avi_port_types` (`ASyntax.hs:593`) — parent-BA content. Natural fix: the primitive performs them from contract data. Also, §12.1 step 3's "compare the replacement IDef" is vacuous (the two IDefs are intensionally different terms; comparison starts at post-iExpand parent dumps). *(evaluator F8 + ba F6)* |
| m6 | The §7.3 audit, performed: of the 8 DefFun inputs (`GenWrap.hs:137-139`; call site `bsc.hs:977-985`), **six are BA-present or symtab-derivable** — `VWireInfo` (`apkg_external_wires`), `VSchedInfo` (verified unmutated between the deffun call and the BA write), `VPathInfo`, `[VFieldInfo]`, pragmas, flags, `abmi_oqt`, plus `fwrapper` (stored as `apkg_is_wrapped`, `AConv.hs:313`). The two stored nowhere are exactly §7.3's pre-named items (F-A9, m7). Also confirmed: the wrapper consumes **only** `asi_v_sched_info` out of `AScheduleInfo`, so §14's "minimal schedule projection" is genuinely small — modulo F-A5. *(ba F1 — this is substantially a supportive result)* |
| m7 | `true_ifc_ids` is a mid-pipeline ISyntax observation (computed post-`iInline`, `bsc.hs:732, 976`, and even `inlineISyntax`-flag-dependent) stored in no artifact — a *fourth* storage category ("captured during the provider pipeline, added to the BA") that §7.3's trichotomy and §2.2's "boundary shape exists before elaboration" both miss. Decide §14's ready-encoding row in favor of capture-and-persist at `bsc.hs:976`; permit derive-from-APackage only with a full-testsuite set-equality proof. *(ba F3, WEAKENED — the §14 row names this datum verbatim)* |
| m8 | §7.1's port/wire row omits concrete `VModInfo` components the parent consumes: clock ancestry/siblings (`VModInfo.hs:353-365`), gate ports with `VPinhigh`/`VPouthigh` semantics, reset-clock association, `vf_mult` port replication, per-method `vf_clock`/`vf_reset`, per-arg clock/reset, `clockCrossingMethods` (`SchedInfo.hs:46`). All BA-present; use as the audit's schema checklist. *(ba F5)* |
| m9 | Evidence-dependency granularity: consumer-side evidence loading drags whole-`.bo` transitive closures (`BinUtil.hs:95-99` + `FixupDefs.hs:34`); typed-slice export with FV closure is new work (though typed-IExpr serialization exists, `GenBin.hs:611`). §14's row is under-sized; add the stress row "WrapField instance calls a private helper two packages away". *(artifacts F1, WEAKENED — §6.3/§7.1/§14 already lean to storing)* |
| m10 | Artifact naming is unspecified: `.ba` files and RTL module names are keyed by the unqualified basename (`bsc.hs:700, 1009`; `GenWrap.hs:1518-1521`; `ABinUtil.hs:487-492`), the meeting rejected mangling, and §6.4 allows multiple BAs per module. "Distinct contracts" is achievable (qualified identity, §7.1); "no artifact collision" needs a naming/indexing decision plus a stated link-plan rule (e.g. deterministic rejection of same-RTL-name providers). The meeting's own suggestion (digest-named artifacts + manifest database, 01:11:51) is a candidate. *(artifacts F5)* |
| m11 | Flags policy unstated: the full 134-field `Flags` record is serialized into every `.ba` (`GenABin.hs:549-564`), `.ba` loading requires exact version equality (`ABinUtil.hs:512`), and §7.4 never says flags are not digest inputs. Add the explicit statement plus a Flags-partition audit (which fields can alter any §7.1 field). *(artifacts F6)* |
| m12 | Format-tag plan missing: the BA gains a boundary-shape record and a third versioned format appears, amid three in-flight branches contending on `.bo`/`.ba` tags. Land the boundary-shape record as a self-versioned optional section; coordinate re-keying order. *(artifacts F7 + spec DOC-5 prong)* |
| m13 | The differential comparator is the one artifact no phase builds: `.ba` byte-identity is unattainable (embedded `Flags`, `abmi_path`, positions, version string — `ABin.hs:37-65, 193-197`), and the §12.1 dumps mostly already exist (`Flags.hs:205-257`). Name the position/flags/path-erasing structural normalizer as a Phase 0 deliverable, shared with the §7.4 canonicalization; restate invariant 8 as "same *normalized* parent BA". *(compat MIG-5)* |
| m14 | Redaction as a distribution mode: nothing in-tree markets source-free `.bo` shipping as IP protection (the vendor story is import-BVI, `user_guide.tex:726-739`), but it is factually possible today and the "never redacted" outcome withdraws it at Phase 3, with the replacement (signature + contract + backend object, which §9.2 shows is *better* for this use) arriving only at Phase 4/5. Acknowledge the capability change and the transitional gap in §2.4 or §9.1. *(compat MIG-6, question)* |
| m15 | Falsifiability hygiene: §14.1's "add the datum" remedy policy needs cost accounting — freeze a normative v1 contract field schema before Phase 0; log every field added during stress testing as a strike against §7.3's sufficiency claim, each with a demonstrated §12.3 invariance proof. (The "unfalsifiable" charge itself did not survive: §12.3's implementation-invariance tests do catch silent widening.) *(spec DOC-6, WEAKENED)* |
| m16 | §6.3's "prove that the consumer's inverse adapter is the inverse" contradicts §11.2's explicit disclaimer; the supportable claim is evidence identity/replay. Also add a §9.3 row for "serialization fix: bytes change, semantics don't". *(spec DOC-7)* |
| m17 | Stress-matrix gaps beyond F-A11: two-level contract-of-contract composition (transitive digest chaining + middle-level dependency cutoff — §6.4/§7.4 make composition part of the design but no row tests it) and String/Real param-only arguments (`IExpandUtils.hs:393-394`, `IExpand.hs:867` — no Bits, no SplitPorts instances). *(spec DOC-8)* |

---

## Part II — Supportive review

### What the document gets exactly right (all verified against source)

1. **The §3 account of current behavior is literally accurate.** The DefFun continuation
   description matches the code down to the parameter list (`type DefFun = Bool -> VWireInfo
   -> VSchedInfo -> VPathInfo -> [VPort] -> SymTab -> [VFieldInfo] -> [Id] -> IO CDefn`,
   `GenWrap.hs:137-139`; closure over pre-typecheck state at `:1461`; invoked post-scheduling
   at `bsc.hs:977-985`). BA-before-wrapper ordering: confirmed (`bsc.hs:963` vs `:971`).
   ABinModInfo inventory: field-for-field (`ABin.hs:44-68`). The second typecheck is a bona
   fide frontend re-entry with its own dump stages (`compileCDefToIDef`, `bsc.hs:2192-2219`).
   This matters because the whole design is a factoring argument — it is only sound if the
   thing being factored is characterized correctly, and it is.
2. **§3.4's stopping rule is a faithful transcription of `genIfcField`** for the cases it
   covers, including the subtle one the proposal calls out (interface-valued method *with
   arguments* is a leaf) and §5.3's synonym-expansion and symtab-identification steps
   (`GenWrap.hs:866-931, 1680-1698`). (The divergences are the vector-of-Clock/ListN/RDY cases
   in F-A11 — real, but at the edges, and exactly the kind of thing the proposal's differential
   plan exists to catch.)
3. **§3.5's complaints are the maintainers' own complaints.** Three FixupDefs XXX comments map
   onto three table rows (`FixupDefs.hs:28-30, 47-50, 76-77`); the backend-leak row is
   literally true (`bsc.hs:946-961`, including the comment lamenting the Bluesim asymmetry);
   §8.2/A.3 is a direct, targeted answer. This is grounded critique, not taste.
4. **Appendix B's file map is accurate** — every named function exists with the claimed role,
   so Phase 0 instrumentation can start without archaeology.
5. **§5.4's extensibility table maps one-to-one onto the real Prelude classes**, including the
   default delegation chain (`Prelude.bs:4551, 4640, 4653, 4702, 4781, 4867`). Reusing the
   user-facing classes as the boundary ABI rather than inventing a parallel serializer is the
   design's best structural decision: user customization keeps working by construction, and
   the differential tests get a fixed semantic target.
6. **The BA-sufficiency claim survives its own audit.** Six of eight DefFun inputs are
   BA-present or symtab-derivable (m6), the wrapper consumes only `asi_v_sched_info` from
   `AScheduleInfo` (so the minimal schedule projection is genuinely small), and the two
   stored-nowhere inputs are the two §7.3 pre-named. The proposal predicted its own exceptions
   — strong evidence the author read the code before writing the claim.
7. **The differential-oracle plan (§12) is well-staged**: each step isolates one mechanism
   change, the failure taxonomy is drawn from real artifacts (the constant-ready row matches
   `true_ifc_ids`; the schedule-failure row matches `ABinModSchedErr`), and for a design whose
   stated preferred outcome is a precise counterexample, this plan is the machine that produces
   one. Indeed, this review's static findings (F-A5, F-A11) are instances of §12.4's own
   categories, found early.
8. **Disciplined scoping.** §4.4's exact-identity-before-compatibility deliberately avoids the
   open-ended hard problem while capturing the cache win; §2.4's non-goals pre-empt scope
   creep; §11.3's source-is-not-a-late-provider argument is real and correct; §14.1
   concentrates risk into one falsifiable claim with a stated remedy hierarchy.

### Alignment with the meeting and the org (verified against the transcript)

9. **The canonical-BO commitment is the meeting's central want, faithfully implemented** —
   including Julie's clarified sense of "personalities" (synthesized vs unsynthesized
   definitions, 01:00:40), encoded as §2.3's first principle, invariant 11.1-1, and Phase 3.
10. **Contract-as-dependency and dependency cutoff turn the meeting's caching insight
    (00:47:21–00:50:27, 01:16:05) into testable requirements** (§7.2, §9.3, §12.3) — an
    upgrade from aspiration to falsifiable plan.
11. **Two subtle meeting distinctions are preserved verbatim**: source-is-not-a-late-provider
    (00:45:33 → §2.4/§11.3) and opacity-choice vs provider-choice (Julie, 01:26:41–01:28:04 →
    §8.4/§B.1). A lossy write-up would have dropped both.
12. **§B.1's five meeting-derived constraints all check out** against specific transcript
    moments (00:58:03 store-aside idea; 01:07:56 atomic actions; 01:04:03 separability), and
    §B.1 is careful to claim only "motivation", not decision.
13. **§8.4 respects the deferred legacy-behavior decision** — hermetic core actions,
    convenience routed to a driver the meeting explicitly postponed to a future proposal, with
    Julie's inline-attribute idea acknowledged as future work.
14. **Everything beyond the meeting answers the meeting's own declared open question** ("the
    missing piece is how do you redact things after elaboration", 00:45:33/00:47:21; "the thing
    that is missing is some real understanding of these module headers or contracts", 01:21:42)
    — and the exact-digest v1 narrows the meeting's looser compatibility talk into something
    buildable without foreclosing the link-time-selection ambition (Phase 5).
15. **Strong alignment with the org's CtxRed-audit direction**: `BoundaryShape` (§A.1) *is*
    the "one concrete boundary description" the audit called for, and §6.3's "this is data, not
    a suspended continuation" is the right instinct — the gap is only that the proposal never
    says so or addresses GenWrap's current `cCtxReduceDef` dependence (F-A1).
16. **It serves the org's top performance demand** — the §9.2 DAG puts canonical-BO production
    before elaboration (early `.bo` availability, the meeting's 00:09:34 critical-path
    complaint), and removing the per-module wrapper re-typecheck cuts measurable CPU
    (`DFwrapper_ctxreduce/typecheck` stages exist today to quantify it). It just never says
    this out loud — see suggestion S4.

### Suggestions (constructive, non-blocking)

- **S1.** Add the prior-art section (F-A15) — one appendix page satisfies the standing org
  decision and would have pre-answered F-A6, F-A10, F-A13, and F-A19.
- **S2.** Connect boundary-shape derivation explicitly to the CtxRed-removal direction: state
  whether Phase 1's derivation retires GenWrap's `cCtxReduceDef` dependence — free alignment
  credit with an existing org decision, and it forces the F-A1 design decision.
- **S3.** Add the format-tag/coordination subsection (m12): optional self-versioned BA
  section; sequencing against the VTA, pattern-match, and verilator tag bumps.
- **S4.** Add the performance analysis §13.1 deserves: the eliminated wrapper stages are
  measurable per synthesized module today; canonical-BO-before-elaboration is the org's
  early-`.bo` ask; serialization/digest costs cut the other way. Make "canonical BO available
  before elaboration completes" an explicit exit criterion.
- **S5.** Specify failure-path parity: poison pills (F-A18) and error exit semantics under the
  canonical-BO model; define what a partially-failed multi-module run produces.
- **S6.** Address the ATF cache in the fixup redesign: `FixupDefs.hs:44-50` documents why
  cache unions live outside `fixupDefs` (per-module re-invocation); A.3 changes that premise —
  one sentence saying where cache unions live in the new model prevents rediscovering the trap.
- **S7.** State whether Julie's per-use-site inline attribute is *expressible* under the
  per-definition overlay (one `BindingChoice` per qualified name per elaboration cannot mix
  inlined and opaque instantiations of one module in one parent) — or scope per-use-site mixing
  out in §2.4 so the future ergonomics proposal knows what the core model supports.
- **S8.** Record Julie's contract-as-declared-expectation-check use case (01:09:27, strongly
  endorsed in the meeting) as acknowledged future work: the exact contract already carries the
  schedule/path/ready sections such a check would diff against; one line in §13/§14 keeps the
  door visibly open.
- **S9.** Name the on-disk artifact naming scheme (m10) — qualified paths or the meeting's own
  digest-named-artifacts-plus-manifest idea — reaffirming that only backend Verilog names
  remain flat.

---

## Part III — Priority list for v0.2

**Must resolve before implementation (blocking):**
1. The evidence-construction mechanism: which compile materializes the boundary shape, from
   which environment, with what machinery (F-A1). This is the single biggest unknown and it
   decides Phase 1's real scope.
2. Migration sequencing: a bridge for cross-package opacity between Phase 3 and Phase 5
   (F-A2), and the pragma-semantics decision (F-A7) that determines what the bridge must
   preserve.

**Decide now, cheaply, from facts this review established (each closes a §14 row):**
3. Module arguments: bespoke per-argument adapter data; SplitPorts/WrapPorts for method ports
   only (m1). 4. `true_ifc_ids`: capture at `bsc.hs:976`, persist in the BA (m7).
5. Target type: store it — including the pre-`fixupPolyModType` polymorphic source type
   (F-A3). 6. Evidence representation: embed the typed closure in v1; defer references+hashes
   (F-A10). 7. Schedule projection: digest method pairs/direction; rule ids non-digested or
   dropped (F-A5). 8. `veriPortProps`: pick the sanctioned-deviation or backend-annotation
   option, and name which oracle personality parity targets (F-A9). 9. Digest composition:
   semantic digest vs format/compiler-version key (F-A13).

**Document work:**
10. Prior-art section (F-A15). 11. Performance exit criteria + Phase 3 rollback flag (F-A14).
12. Contract-validation subsystem as a named deliverable (F-A12). 13. Per-backend split of
§9.1/§9.3 with the Bluesim correction (F-A16). 14. `noinline` design or explicit v1 scope-out
(F-A4). 15. Dependency-cutoff limitation + `ipkg_depends` replacement (F-A17). 16. The three
completeness items: poison pills, cross-contract evidence coherence, instantiation-time
diagnostics (F-A18–20).

**New stress-matrix rows implied by findings:** `Vector#(n,Clock)`/`ListN` fields;
poly-field subinterfaces; rename-an-internal-rule (digest stability); blank-line/helper-rename
(digest stability); custom SplitPorts instance on a module-argument type (ABI must NOT
change); String/Real parameters; two-level contract composition; two contracts with divergent
evidence closures; poison-pill flows; instantiation-error parity; per-use-site mixed
inline/opaque (or its explicit rejection).

---

## Addendum (2026-08-22/23) — The picked-strategy design: pick the boundary, don't compute it

Recorded from the post-review design dialogue with Ravi. Status: **ratified design direction
for v0.2**, not yet incorporated into the proposal document itself. The CtxRed retirement
plan's §5 coordination map references this design; this addendum is its full statement.

### The move

Ravi's reframing: **you don't compute the new interface, you pick it.** The core relation is
`Wrap c a` with associated type function `Boundary c a = b` and `toB`/`fromB` methods — the
instance is told it is wrapping a specific `a` to a specific `b` via strategy `c`, "and then
`c` is where all the fun is." This converts F-A1's root cause from "must re-run open-ended
inference" into "check a ground relation."

Why ground checking already exists as pure, reusable machinery: `matchTop` (`TCMisc.hs:789`)
is a plain function outside the TI monad whose return value includes the per-instance fundep
substitution — "read the output type off the matched instance head" is a single call, no
fixpoint. The symtab's `Class` record carries `genInsts`, a trie indexed by the fundep *input*
positions (`Pred.hs:135-152`), and each `Inst` carries its evidence `CExpr` and source package
(`Pred.hs:215` — exactly what §5.5's defining-environment rule and evidence-identity recording
need). Where "computing" seems to sneak back in — a custom `SplitPorts a p` instance
legitimately determining part of the boundary type — it degrades to a one-shot ground read:
`a` is ground at every leaf, so the chain grounds itself top-down (`SplitPorts a p` match →
`p` ground → `WrapPorts p pb` match → …). What CtxRed provided was a *fixpoint over floated
constraints*; picking eliminates the floating, so no fixpoint is ever needed.

BSC's ATF machinery is the exact enabler (correcting an in-dialogue misstep that claimed BSC
lacks type families): `TIatf` is a TyCon sort carrying `atf_class_id`/param-idxs/target-idx
(`CType.hs:127`) — a type function is a pointer at its owning class plus the fundep
projection. Resolution is not a separate mechanism: when `sat` solves the owning class's
constraint, `recordATFs` projects and memoizes `(atfId, ground args) → result`
(`TCMisc.hs:326-333`). "Solve but no search" is *enforced*: instance heads may not contain
type functions (`MakeSymTab.hs:447-461`), so evaluation is well-founded — no matching on
function results, no backtracking, a unique match at ground inputs. And the solves are
memoized in a serialized artifact: `ipkg_atf_cache :: Map (Id,[IType]) IType` in the `.bo`
(`ISyntax.hs:136-144`) — more or less the boundary-shape record's type-level half, format
included. `Boundary c a = b` entries are the `(a, b, c)` table, keyed the way the compiler
already keys them.

### The F-A1 answer (which compile, from which environment)

- The strategy pick runs at **provider-BA time**, needing only the symbol table, instance
  tables, and pragmas — all reconstructible from `.bo` signatures post-BO-load. The per-leaf /
  per-argument `(a, b, c)` assignment **is** the boundary-shape record; consumers replay from
  the record with no lookup. "Resolve once, replay exactly" becomes almost trivially true:
  **pick once, record, replay.**
- The one residue: the cache won't pre-contain `Boundary c FooIfc` for a module no source ever
  uttered, so the provider-BA action still evaluates at pick time — with a named shape: either
  a scoped one-constraint TI run (tiny; the monad resets per top-level def anyway) or a pure
  ground evaluator reusing `matchTop` + the fd projection. A line item, not an open question.
- **Correctness constraint on the ground-discharge engine:** it must reproduce the
  typechecker's instance-*ordering* and coherence semantics exactly — reuse `genInsts` +
  `matchTop` + the `allowIncoherent` handling rather than reimplement; any divergence is a
  silent evidence mismatch the differential plan must gate. Evidence assembly is
  syntax-directed recursive descent building application spines over instance defs — ordinary
  named `.bo` definitions (`mkInstId`) — not a `reducePred` reimplementation.
- **Design rule:** the `Wrap`/`Boundary` classes must be declared always-coherent
  (`allowIncoherent = Just False`) or the replay guarantee evaporates. The ATF cache's
  coherent-only recording discipline is §5.5's consumer-must-not-re-resolve rule already
  implemented at the type level.

### What the strategy index buys beyond F-A1

- **Evidence identity (softens F-A10/TC-3):** the frozen evidence becomes a nameable per-leaf
  table of `(path, a, b, c)` plus ground instance references instead of an opaque dictionary
  graph; only the user-defined leaf-strategy (`c`) instances still need embedding or
  fingerprinting; the structural walk is replayable-by-construction.
- **Module arguments (m1):** the bespoke compiler logic gets a uniform form — `ViaBits`,
  `ViaClock`, `ViaParam`, `ViaInoutCast`, `ViaVecBlast` as compiler-picked argument
  strategies. Same vocabulary as method ports, no pretense that SplitPorts covers them.
- **The stopping rule (F-A11):** RDY-field synthesis, vector-of-Clock/ListN recursion, and
  poly-field leaves become explicit *picker policy* — where they already de facto live in
  `genIfcField`. §2.3's slogan gets a version the code can satisfy: the compiler picks
  structure *and strategy*; classes witness the conversion at the picked strategy.
- **Coherence (TC-6/§10.1):** strategy-indexed instances are disjoint by construction; user
  override means picking a different `c`, not racing an overlapping instance against the
  compiler-derived one. The `BoundaryIfc` facade and possibly `mkGeneric` shrink or disappear —
  adapters assemble directly from strategy methods.
- **TC-6/m3 name collisions dissolve by ATF direction:** the ATF runs `(c, a) → b`, so
  boundary-type identity is the (strategy, source type) pair and `b` never needs to determine
  anything — the collision concern dissolves rather than needing m3's structural
  content-addressing patch.
- **Closes the catch-all-plus-shadowing idiom for boundary classes.** BSC commits on head
  match with no backtracking, so `instance (WrapMethod m w) => WrapField name m w`
  (`Prelude.bs:4653`) captures everything, and the Clock/Reset/Inout specials (`:4672-4677`)
  exist only to win the specificity race — "keep Clock away from WrapMethod":
  dispatch-by-shadowing, under committed matching, in an open world. Under picks, the former
  catch-all becomes the *total instance of one strategy* (`Wrap m w ViaWrapMethod`), genuinely
  coherent-and-closed within its head; Clock needs no pre-empting instance because the picker
  picks `ViaClock`. The extension axis rotates: customization means adding a new strategy type
  with its instances, which can never invalidate an existing match — growth becomes monotone;
  world-closedness without sealing the world (extension made orthogonal to selection). Error
  quality flips from a context failure three classes deep to "strategy `ViaWrapMethod`
  requires `Bits` for T at field F" — the pick is in the message. Ecosystem corroboration: the
  June port-splitting decision (no splitting by default; `SplitVector` as an explicit wrapper
  when wanted) is behavior-selected-by-type — the strategy pattern avant la lettre.

### Migration and residues

- **§5.4 compatibility bridge:** today's `WrapField`/`WrapMethod`/`SplitPorts`/`WrapPorts`
  instances keep working because default strategies are *delegating instances* —
  `(WrapMethod m w) => Wrap m w ViaWrapMethod` — and the picker selects those defaults unless
  told otherwise.
- **Within-strategy no-overlap rule:** the closure is only as good as the no-overlap
  discipline *within* a strategy — overlapping `Wrap SpecialT w' ViaWrapMethod` against a
  strategy's total instance brings the open-world hazard back locally. Design rule: customize
  by new strategy, never by overlapping an existing strategy's instances — enforced by the
  closed-class marker applied per strategy head (the same marker the CtxRed plan wants;
  double duty), or at minimum a warning.
- **Per-field customization (explicit v0.2 decision):** today's path-keyed
  `WrapField name ...` instances either become a pick annotation at the field, or survive as
  *inputs to the picker* (a one-shot ground lookup — no longer racing hazards either way). The
  choice is between "instances as configuration the picker reads" and "annotations as
  configuration" and must be made explicitly in v0.2.
- **Untouched by this design:** the post-elaboration data (`true_ifc_ids`, `veriPortProps`),
  digest normalization, and the F-A2/F-A7/F-A8 migration-sequencing findings all stand.

### Prior art

The shape is precisely GHC's **DerivingVia + deriving strategies**: `c` is the via-type, and
GHC chose *explicit* strategies for exactly this reason — route inference among overlapping
derivation methods is ambiguous. The delta: GHC's via leans on `Coercible`, which BSC lacks,
so the witness here is a real conversion instance rather than a coercion — arguably more
honest for a hardware boundary. (This addendum discharges part of F-A15's prior-art
obligation for the affected sections; the full literature pass v0.2 owes is unchanged.)

### Effect on this review's verdict

With picked `c`, `Boundary` as an ATF, and ground-instance evidence discharge, **F-A1 drops
from critical to resolved-by-design-change once v0.2 writes it down** — a specifiable §5
rewrite naming existing machinery plus one small evaluator. **F-A2 (Phase 3 stranding
cross-package opacity) becomes the sole standing blocker.** The A.3 fixup redesign concretely
owns ATF-cache union duties (`FixupDefs.hs:47-50`; review m4/S6). Part III item 1 should be
read as answered by this addendum; item 3 (module arguments) as reshaped into the argument
strategies above.

---

*Review conducted 2026-08-22 against B-Lang-org/bsc @ 941eecf. Six adversarial lenses, each
independently verified; two supportive passes; completeness critic; ~1.9M tokens of
code-grounded analysis across 15 agents; verdict disputes resolved by direct source
inspection. Addendum recorded 2026-08-23 from the post-review design dialogue.*
