# Handoff: issue to open on B-Lang-org/bsc

This document is the draft for a GitHub issue proposing that orphan
typeclass instances be rejected for `Bits` and `SplitPorts`.  The test
directory containing this file is the supporting evidence: every scenario
described below is checked in as a passing test against current bsc,
demonstrating that the toolchain accepts each mislink without a diagnostic.

Everything below the line is issue-ready text.

---

**Suggested title:** Orphan instances of `Bits` and `SplitPorts` produce
silently mis-linked hardware; they should be errors, not a warning

## Summary

`Bits` and `SplitPorts` are unlike every other typeclass in the library:
their instances are baked into generated hardware artifacts.  When a module
is synthesized, the wrapper machinery (`WrapMethod`/`WrapPorts` in the
Prelude, inserted by `GenWrap`) resolves `splitPorts`/`portNames` to decide
**which Verilog ports exist and what they are named**, and `pack`/`unpack`
to decide **the bit layout on each port** — using whichever instances are
visible in the import cone of the package being compiled.

An orphan instance (typeclass and all head types defined elsewhere) makes
that resolution a property of the *import graph* instead of the *type*:
two packages in one program, or two builds of one design, can resolve the
same predicate differently.  Each resolution is locally coherent, so no
compile has anything to report — but the divergence is physically real in
the netlists, and it surfaces exactly where nothing checks it: raw
`Bit#(n)` channels and name/width-based Verilog integration.

bsc already acknowledges the problem: it warns (T0127) when an orphan
instance is exported.  The warning is at the wrong site (the definition,
not the many use/absence sites where wrong hardware is generated), it is
suppressible, and — as shown below — the rest of the diagnostic machinery
is structurally unable to catch the resulting mislinks.  For these two
classes the failure mode is silent data corruption in hardware, so the
warning should be an error.

## Demonstrations

The branch adds `testsuite/bsc.typechecker/instances/orphan_mislink/`:
four scenarios that *should* fail, each currently compiling, linking, and
simulating cleanly (63 harness assertions, Bluesim + iverilog).  Each test
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

**Case 3 — `SplitPorts`, Verilog top level, identical pinouts with
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

**Case 4 — `SplitPorts`, pure Bluespec, orphan *absence* is
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

## Why every existing defense misses

* **T0127 (orphan warning)** fires at the orphan's export site only, is
  suppressible, and says nothing at absence sites — which look perfectly
  normal and are where the wrong artifact is generated.
* **T0099 (duplicate instance)** requires both instances in one symbol
  table.  Hardware integration happens in Verilog, where there is no such
  compile; and the specialization-vs-generic overlap (Case 1) is legal
  even when both *are* visible.
* **`class coherent Bits`** polices incoherent *matches* within one
  resolution site; every match in the cases above is locally unambiguous
  and coherent.
* **T0157 (unused import)** is actively counterproductive here (Case 3/4).
* **Typed BSV connections mask the problem**: when two synthesized modules
  with divergent encodings are connected at the BSV level, each wrapper
  pairs its own `pack`/`unpack`, and elaboration silently materializes
  layout-A→layout-B permutation logic.  The design "works in simulation,"
  which is precisely what builds false confidence — while every type-erased
  path corrupts, and the netlist carries two different wire layouts for one
  struct plus gratuitous rewiring logic (a surprise for equivalence
  checking and debug).

## Why a ban is the right fix, and why it costs nothing

Rejecting orphans restores the invariant **"naming implies visibility"**:
if an instance must live with its class or with a type constructor of its
head, then any compile that can even *utter* `Bits#(T, n)` or
`SplitPorts#(T, p)` has transitively imported the instance.  Consequences:

1. Every resolution site sees the same candidate set, program-wide and
   across builds compiled from the same sources — Case 1's overlap
   loophole closes (naming `Msg Hdr` forces importing the packages where
   any specialization must now live).
2. True duplicates are forced into a shared compile, where T0099 already
   fires — the ban makes the existing duplicate check *complete*.
3. Pinouts and encodings become a property of the type, not of the import
   graph — Cases 2–4 become impossible to express.

No expressiveness is lost: anyone wanting an alternate encoding or
splitting writes a newtype next to its instance — zero hardware cost, and
exactly the pattern the library itself ships (`ShallowSplit`, `DeepSplit`,
`NoSplit`, `SplitVector` are all newtype tags defined *with* their
instances, precisely so the choice travels in the type).

## Proposal

Make T0127 an error when the instance's class is `Bits` or `SplitPorts`
(including instances reachable through the deriving-style helper classes
used at synthesis boundaries), keeping the warning for other classes.
Implementation options, in increasing generality:

1. Hard-code the two classes in the existing orphan check in `GenSign`.
2. Add a class annotation (e.g. extending the existing
   `coherent`/`incoherent` annotation family with a "no orphans" property)
   applied to `Bits` and `SplitPorts` in the Prelude, so other
   artifact-determining classes (and user libraries) can opt in.
3. A compatibility flag (e.g. `-allow-orphan-instances`) to downgrade the
   error to the current warning during migration, if needed.

## Reproducing

```
git fetch <fork> claude/orphan-mislinks-splitports-bits-c0p7e8
# build bsc into ./inst, then:
cd testsuite/bsc.typechecker/instances/orphan_mislink
make localcheck   # requires dejagnu, csh, iverilog
```

All 63 assertions pass today; under the proposed ban, the orphan-defining
packages (`WireEnc`, `WireEnc2`, `SplitFwd`, `SplitRev`, `ReqSplit`) fail
to compile and every downstream mislink becomes unrepresentable.
