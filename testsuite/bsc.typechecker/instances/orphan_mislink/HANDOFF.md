# Handoff: issue to open on B-Lang-org/bsc

This document is the draft for a GitHub issue proposing that orphan
typeclass instances be rejected for `Bits` and `SplitPorts` (and the other
port-determining classes).  The test directory containing this file is the
supporting evidence: every scenario described below is checked in as a
passing test against current bsc, demonstrating that the toolchain accepts
each mislink without a diagnostic.  Every technical claim below has been
verified against the compiler source and, where empirical, reproduced with
a compiler built from this branch; source references are to this branch.

Everything below the line is issue-ready text.

---

**Suggested title:** Orphan instances of `Bits` and `SplitPorts` produce
silently mis-linked hardware; they should be errors, not a warning

## Summary

`Bits` and `SplitPorts` are unlike every other typeclass in the library:
their instances are baked into generated hardware artifacts.  When a module
is synthesized, the wrapper machinery (`WrapField`/`WrapMethod`/`WrapPorts`
in the Prelude, inserted by `GenWrap`) resolves `splitPorts`/`portNames` to
decide **which Verilog ports exist and what they are named**, and
`pack`/`unpack` to decide **the bit layout on each port** — using whichever
instances are visible in the import cone of the package being compiled.
The resolved dictionaries are frozen into that package's `.bo` and
generated Verilog; client compiles never re-resolve them.

An orphan instance (one defining neither the class nor the head type it
encodes) makes that resolution a property of the *import graph* instead of
the *type*: two packages in one program, or two builds of one design, can
resolve the same predicate differently.  Each resolution is locally
coherent, so no compile has anything to report — but the divergence is
physically real in the netlists, and it surfaces exactly where nothing
checks it: raw `Bit#(n)` channels, `Inout` nets, and name/width-based
Verilog integration.

bsc already acknowledges the problem: it warns (T0127) when an orphan
instance is exported.  The warning is at the wrong site (the definition,
not the many use/absence sites where wrong hardware is generated), it is
suppressible, it can be evaded outright (see the companion defect below),
and — as shown below — the rest of the diagnostic machinery is
structurally unable to catch the resulting mislinks.  For these classes
the failure mode is silent data corruption in hardware, so the warning
should be an error.

## Demonstrations

The branch adds `testsuite/bsc.typechecker/instances/orphan_mislink/`:
five scenarios that *should* fail, each currently compiling, linking, and
simulating cleanly (78 harness assertions, Bluesim + iverilog).  Each test
also pins where T0127 fires: only at the orphan's defining package, never
at a damage site.

**Case 1 — `Bits`, pure Bluespec, zero diagnostics anywhere.**
`WireEnc.bs` defines an orphan `Bits (Msg Hdr) 33` (valid bit at the MSB,
"per the wire spec").  It is strictly more specific than the derived
generic instance `Bits (Msg t) _`, so the pair is a *legal ordered
overlap* — the duplicate-instance check (T0099) can never fire.  `Ingress`
(imports the orphan, possibly transitively) packs with the orphan layout;
the value crosses a `Reg (Bit 33)` — standing in for any FIFO, BRAM, bus,
or DMA descriptor of raw bits; `Egress` (does not import it) unpacks with
the derived layout.  Both backends compute:

```
sent     src=aa dst=bb len=cafe valid=1
received src=d5 dst=5d len=e57f valid=0
ROUNDTRIP CORRUPTED
```

The top-level compile sees *both* instances and still has nothing to say.
`WireEnc2.bs` shows the test-evading variant: an orphan that only swaps
`src`/`dst` roundtrips correctly whenever `src == dst` — loopback smoke
tests pass while real traffic is misrouted.  `OrphanBitsBothCones.bs`
documents the only configuration the compiler *can* catch (equal-head
orphans joined in one symbol table → T0099), which none of the failing
flows reach.

**Case 2 — `Bits`, Verilog top level.**  `mkMsgSource` (orphan cone) and
`mkMsgSink` (derived cone) both expose `Msg Hdr` as a 33-bit port.  A
hand-written Verilog top connects them by name — the standard SoC
netlist-integration step.  Same names, same widths: every tool links
cleanly, and the sink reads `d5` where the source drove `aa`.  This is the
IP-delivery flow: the two artifacts never share a bsc compile, so no
in-compiler check is even reachable in principle.

**Case 3 — `Bits` over `Inout`, pure Bluespec, fully typed connection.**
An `Inout` is the one interface kind where bsc cannot paper over divergent
encodings even in a typed connection.  `mkConnection` on `Inout` resolves
to `vInoutConnect`, a BVI wrapper around `InoutConnect.v` that ties both
sides to the *same net* (the `Bits` proviso contributes only the width),
and the synthesis-boundary handling of an `Inout` field is
`primInoutCast` — a logic-free bit-cast.  There is no direction in which
conversion logic could even be materialized.  A driver in the orphan cone
and an observer in the derived cone, joined by a plain typed
`mkConnection drv.bus obs.bus` — no `Bit#(n)` anywhere in user code —
produce:

```
driver drives  src=aa
observer sees  src=d5
SILENT INOUT BITS MISLINK
```

Notably, this case does not even produce the T0157 unused-import hint of
Cases 4–5: the `mkTriState` proviso consumes the orphan in every compile
mode, so the damage sites are pristine under every diagnostic bsc has.
(Bluesim rejects `Inout` designs with G0097, so this test is
Verilog-only.)

**Case 4 — `SplitPorts`, Verilog top level, identical pinouts with
opposite meanings.**  `SplitFwd.bs` and `SplitRev.bs` are two orphan
`SplitPorts` instances for `Vector 4 (Bit 8)` that emit the IDENTICAL
port-name set (`_0.._3`, positional names, same widths) with opposite lane
mappings.  A producer from one cone and a consumer from the other, joined
by name in a Verilog top, silently cross the lanes:

```
lane 0 sent 11, lane0 method sees 44
SILENT SPLITPORTS MISLINK (lanes crossed)
```

Worse, a plain (non-codegen) compile of the producer/consumer packages
flags the orphan import as **unused (T0157)** — the compiler actively
invites the user to delete the import that determines the module's pinout.

**Case 5 — `SplitPorts`, pure Bluespec, orphan *absence* is
undiagnosable.**  `SplitPorts` has a legal catch-all default instance
(`SplitPorts a (Port a)`, "don't split"), so a compile that cannot see an
orphan silently falls back to the unsplit pinout.  The identical module
body yields `put_1_addr[31:0], put_1_dat[63:0]` in one import cone and
`put_1[95:0]` in the other — two pinouts for the same interface type in
one program (`BothSinks.bs` instantiates both), with no diagnostic even
where the cones join, because a specific instance overlapping the
catch-all is legal.  Any constraints file, DFT insertion, ECO script, or
frozen netlist written against one pinout silently mismatches the other,
and the pinout flips when a *dependency* edits an import list.

The same failure is reachable through the other wrapper classes: an orphan
`WrapPorts (Port Hdr) (Bit 32)` instance (class and `Port` from the
Prelude, `Hdr` foreign) is a legal specialization of the Prelude's generic
instance and rewires the port slicing of a synthesized module while
emitting *identical port declarations* — the exact Case 2 failure without
touching `Bits` or `SplitPorts`.  Any fix must cover the whole
port-determining class family, not two names (see Proposal).

## Why every existing defense misses

* **T0127 (orphan warning)** fires at the orphan's export site only
  (`genDefSign`'s `Cinstance` case — instances arriving from import
  signatures are `CIinstance` and can never warn at a client), is
  suppressible, and says nothing at absence sites — which look perfectly
  normal and are where the wrong artifact is generated.  Precisely: an
  instance is flagged when its class is imported and no type constructor
  in the *fundep-source* part of the head (the `a` of `Bits a n | a -> n`)
  is defined **and exported** by the current package; the compiler warns
  on a strict superset of the intuitive "class and head types all foreign"
  reading, and every instance called an orphan in this issue is flagged
  under both readings.
* **`-promote-warnings T0127` already exists and is not enough.**  bsc can
  make the warning fatal today — but only at the definition site.
  Promoting warnings (even `ALL`) at the damage sites changes nothing:
  the use sites and absence sites have no orphan definition to promote,
  and in the IP-delivery threat model the victim is the downstream
  integrator, who does not control the build of the package that defines
  the orphan.  Case 5 has no orphan definition anywhere in the damaged
  cone at all.  A definition-site-only promotion is structurally unable to
  protect use/absence sites; rejection must be intrinsic to the class.
* **T0099 (duplicate instance)** requires both instances in one symbol
  table.  Hardware integration happens in Verilog, where there is no such
  compile; and the specialization-vs-generic overlap (Cases 1, 3, 5) is
  legal even when both *are* visible.
* **`class coherent Bits`** polices incoherent *matches* within one
  resolution site; every match in the cases above is locally unambiguous
  and coherent.
* **T0157 (unused import)** is actively counterproductive (Cases 4–5), and
  in Case 3 not even that: the compiler is perfectly silent.
* **Typed BSV connections mask the problem — except when they can't.**
  When two synthesized modules with divergent encodings are connected at
  the BSV level through value methods, each wrapper pairs its own
  `pack`/`unpack`, and elaboration silently materializes layout-A→layout-B
  permutation logic.  The design "works in simulation," which is precisely
  what builds false confidence — while every type-erased path corrupts,
  the netlist carries two different wire layouts for one struct plus
  gratuitous rewiring logic (a surprise for equivalence checking and
  debug), and the one connection kind with no direction to insert logic
  into (`Inout`, Case 3) corrupts even fully typed.

## A companion defect that any fix must also close

Adversarial testing of this proposal found a hole in signature generation
that both *evades* T0127 and reproduces these mislinks *without any
orphan*:

`GenSign`'s keep/drop test for emitting an instance into the package
signature runs on the **synonym-unexpanded** instance head (`genDefSign`,
`Cinstance` case: `leftTyCons (t : tyConArgs t)` with no `expandSyn` —
`CtxRed` deliberately preserves synonym spellings in instance heads, per
its own `XXX` comment), while the orphan classification a few lines later
*does* expand.  Consequently an instance whose head is spelled through a
**private local synonym** is silently dropped from the user signature:

* `type MsgH = Msg Hdr; instance Bits MsgH 33` in a package that defines
  `Msg`/`Hdr` (a fully **non-orphan** instance) is invisible to every
  importer: the defining package packs with the specialization, importers
  resolve the same expanded predicate `Bits (Msg Hdr) 33` to the derived
  instance — a Case-1-shaped mislink in a program containing **zero
  orphans**.  The same trick reproduces Case 5's dual-pinout with a
  non-orphan `SplitPorts` instance.
* The same spelling applied to an *orphan* instance evades T0127 entirely
  (the warning is attached only in the signature-kept branch), bakes its
  layout into generated Verilog, and is invisible even to direct
  importers — so making T0127 fatal, alone, rejects nothing.
* The accounting is internally inconsistent: the dropped instance still
  rides in the `.bo`'s internal "everything" signature, so a package that
  merely imports two such packages can die with an unactionable T0099
  naming a type it cannot even utter, while resolution uses a different
  instance set.

This is arguably a distinct bug worth its own report, but the proposal
below is specified to close it, because "the instance must live with its
type" only guarantees coherence if the instance also *travels with* its
type.

## Why a ban is the right fix

Rejecting orphans — together with making signature emission total for
these classes — restores the invariant **"naming implies visibility"**: if
an instance must live with its class or with a type constructor of its
head, *and can never be silently dropped from its package's signature*,
then any compile that can even utter `Bits#(T, n)` or `SplitPorts#(T, p)`
has transitively imported the instance.  Consequences:

1. Every resolution site sees the same candidate set, program-wide and
   across builds compiled from the same sources — Case 1's overlap
   loophole closes (naming `Msg Hdr` forces importing the packages where
   any specialization must now live).
2. True duplicates are forced into a shared compile, where T0099 already
   fires — verified to hold even for duplicates spelled through different
   *exported* synonyms of the same head (`cmpQInsts` compares expanded
   heads).  The ban makes the existing duplicate check *complete*.
3. Pinouts and encodings become a property of the type, not of the import
   graph — Cases 2–5 become impossible to express.

### The migration cost, measured honestly

The escape hatch is a single-constructor wrapper type (a newtype-style
tag) defined next to its instance.  Its **hardware cost is zero**: a
wrapper-based reimplementation of Case 2's source generates a
byte-identical pinout, and the interop adapter between wrapped and
unwrapped interface types elaborates to pure wiring.  Its software cost is
real and should be stated plainly: the wrapper is viral (a custom-encoded
field must carry the wrapper through every struct, interface, and
`deriving (Bits)` that transports it), and wrapping a container type
forfeits the container's instances until re-provided.  Two answers:

* The library already models exactly this pattern and pays exactly this
  cost: `ShallowSplit`, `DeepSplit`, `NoSplit` are wrapper tags defined
  with their instances, and `SplitVector` wraps `Vector n a`, re-deriving
  `Bits` and re-providing `Functor`/`Foldable`/`Traversable`/
  `PrimSelectable` so the wrapper is not lossy in practice.  The ban asks
  users to follow the idiom the standard library already ships.
* The "viral" reconciliation is not new cost — it is the *same* conversion
  that elaboration already conjures silently at every typed boundary
  between divergent encodings (see "masks the problem" above).  The ban
  forces that adapter to be named and visible instead of implicit, which
  is strictly better for equivalence checking and debug.  The one
  irreducible case — a custom encoding against a pre-synthesized black-box
  IP whose pinout is fixed — requires an explicit adapter module under
  *any* orphan rule; no instance anywhere can change already-frozen ports.

And non-compositional `deriving` is the point, not a regression: under
orphans, `deriving (Bits)` on a struct is already silently
import-graph-dependent for any field with an orphan encoding; under the
ban it is deterministic.

### Blast radius, measured

* **Shipping libraries: zero orphan `Bits`/`SplitPorts` instances.**
  Every `instance Bits` and `instance SplitPorts` in `src/Libraries` has
  its head type (or the class) defined in the same package, confirmed both
  by static sweep and by a full clean rebuild of all 128 library packages
  (one T0127 total in the tree, and it is `Eq`, not `Bits`/`SplitPorts` —
  see below).
* **Testsuite: zero currently-passing tests affected.**  All existing
  T0127-expecting tests are orphans of *other* classes (`Functor`,
  `Bounded`, `Connectable`, user classes) and keep their warning under a
  class-specific ban; every `instance Bits`/`instance SplitPorts` in the
  suite (~57 sites) defines its head type in the same file.  The only
  code in the repo the ban rejects is this directory's own demonstration
  packages.
* **A blanket "all orphans are errors" would break the library**:
  `Base2/EqFunction.bs` ships an intentional orphan `Eq (a -> b)` whose
  whole purpose is to be an orphan.  This is the concrete argument for a
  class-scoped rule rather than a global one.
* bsc's orphan test is already permissive in the right way: an instance is
  non-orphan if *any* tycon in the fundep-source head is local-and-
  exported, so `instance Bits (Vector n MyLocalType) _` and every
  wrapper-based override remain legal.  Only in-place re-encodings of
  fully foreign types are hit — which are precisely the hazardous ones.

### Precedent

GHC ships orphan instances as a warning — but GHC can afford leniency
because it has a whole-program safety net: every instance transitively in
scope is merged into one instance environment when modules are linked into
a single program, so conflicts surface at the final link.  bsc's Verilog
output has no final link (Cases 2 and 4: the artifacts never share any
compile), so the one mechanism that makes GHC's stance safe is
structurally absent for hardware.  Rust, whose separate-crate model
matches bsc's separate-package reality, made the orphan rule a **hard
error** (E0117) precisely to get global coherence without a whole-program
check — and the newtype pattern is its accepted workaround.  The stakes
differ categorically, too: GHC orphan incoherence yields a recompilation
hazard or a link-time type error; bsc orphan incoherence yields a chip
that computes wrong answers.

### Alternatives considered (and why they don't close the holes)

* **"Cross-check layouts at `bsc -e` / `.ba` link."**  The `.ba` records
  each port's *source type* and *width*, not the resolved layout: the two
  divergent modules of Case 2 record identical `Msg#(Hdr)`/33-bit port
  entries (verified via `bluetcl` porttypes), so the checker would have
  nothing to compare without first serializing a layout fingerprint — and
  the IP-delivery flow never assembles both sides in one invocation
  anyway.
* **"Embed a layout hash in port names / netlist attributes."**  This
  destroys the stable-pinout contract that constraints files, DFT, and ECO
  scripts key off (a hash flips whenever a dependency edits an import —
  inflicting Case 5's failure mode on every design); it cannot help Case 1
  (no ports involved) or Case 3; attributes are dropped by many flows; and
  it cannot distinguish an intended alternate encoding correctly adapted
  from an accidental mismatch.
* **"Verify encodings at Verilog link time."**  The layout is not
  expressible in the generated Verilog at all — both modules declare
  `[32 : 0]` ports with identical names; the divergence lives in internal
  bit-slicing — and the join happens in third-party tools where no bsc
  invocation exists.
* **"Reject only orphans that reach a synthesis boundary."**  Unsound:
  no single compile sees both the instance and the boundary in the
  cross-build case, and "never touches hardware" is not a safe category —
  Case 1 corrupts through an internal register, not a port.  The
  definition site is the only point that every affected build provably
  passes through.

## Proposal

Reject orphan instances of the port-determining classes, via a class
property rather than hard-coded names:

1. **Mechanism**: extend the existing class-annotation family (the
   `coherent`/`incoherent` flag already carried by class declarations)
   with a "no orphan instances" property, checked where T0127 is computed
   today (`GenSign`), but as an error.  Apply it in the Prelude to `Bits`,
   `SplitPorts`, and the wrapper family (`WrapField`, `WrapMethod`,
   `WrapPorts`) — every class whose instances are baked into ports — and
   let user libraries opt their own boundary classes in.  Orphans of
   ordinary classes (`Functor`, `Bounded`, `Eq (a -> b)`, …) keep the
   plain warning.
2. **Close the companion defect in the same change**: run both the
   signature keep/drop test and the orphan classification on the
   `expandSyn`-ed instance head, and for annotated classes make silent
   omission from the signature an error as well — an instance of these
   classes must be *exported*, not merely non-orphan.  (Expanding heads
   uniformly also resolves the `CtxRed` `XXX` and makes the duplicate
   checker, the resolver, and the signature agree on one head.)
3. **Migration**: a flag to downgrade the new errors to the current
   warning during transition (note `-promote-warnings T0127` already
   exists for teams who want definition-site strictness today, but it
   cannot protect use/absence sites and evasion-spelled orphans — the
   error must be intrinsic).

## Reproducing

```
git fetch <fork> claude/orphan-mislinks-splitports-bits-c0p7e8
# build bsc into ./inst, then:
cd testsuite/bsc.typechecker/instances/orphan_mislink
make localcheck   # requires dejagnu, csh, iverilog
```

All 78 assertions pass today; under the proposed ban, the orphan-defining
packages (`WireEnc`, `WireEnc2`, `SplitFwd`, `SplitRev`, `ReqSplit`) fail
to compile — including when respelled through private synonyms, per
proposal point 2 — and every downstream mislink becomes unrepresentable.
