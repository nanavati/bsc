# RFC: Polymorphic Scheduling

Schedules as types, values, and contracts.

**Status:** Draft v0.2 — 2026-08-23. Unifies two arcs that reached the
same summit independently: the *value side* — §§14/14.b/14.c of
`RFC-bsc-artifact-graph.md` (a design discussion, Ravi Nanavati with
Claude) — and the *type side* — the scheduling-as-types arc of the
scheduling-complexity session, whose companion implementation (the
scheduler pair-enumeration transpose) landed as MatX-inc bsc PR 47.
Not proposed upstream. The artifact-graph RFC's §§14–14.c remain as
the summary; this document is the full treatment. v0.2 resolves the
urgency-axis question by ruling (§5.b): the new model has **one
order** — the urgency/execution distinction is dropped; fancier
arbitration is written down explicitly.

---

## 1. Summary

Scheduling becomes a first-class dimension of the language, with the
same structure types have:

- **A permissiveness lattice** orders schedules; the compiler infers
  the **precise** (principal) schedule; designers write **declared**
  schedules checked by **subsumption**; schedule variables quantify
  with lattice bounds. (§3)
- **Intra-cycle position becomes a kind.** Reads, writes, and methods
  carry position *variables* constrained by relational provisos
  (`Before#` and kin) — deliberately with no literals and no
  arithmetic. Concrete positions are solver *output*, never source.
  The machinery is the proviso/SMT engine bsc was born with. (§4)
- **Schedules are values**: a Schedule value is a *binding of position
  variables*. The pragma surface demotes to constructors of that
  value; the fill/verify dial (none / partial / total) is how much of
  the solver's model the designer pins. (§5)
- **Footprints are the contract representation.** The linear-size
  object a module exports is *what it touches, how, at which
  positions*; every pairwise relation (SchedInfo, conflict matrices)
  is a derived view. Persist generators, not views. (§6)
- **The EHR dissolves.** A position-polymorphic register — `read@p` /
  `write@p` with the EHR laws as axioms — is the free object of the
  theory; the EHR is its shadow in a monomorphic language. One
  polymorphic FIFO text yields pipeline, bypass, and CF variants by
  constraint resolution alone. (§7)
- **Specification changes the objective, not the asymptotics.** The
  quadratic was an implementation artifact (fixed, bit-identically, by
  the resource-indexed transpose — PR 47). What specification buys is
  replacing the maximize-firing objective with stated intent, and
  demoting SMT exclusion proofs to assertions. (§8)
- **Binding time becomes a design axis**: ordering contracts bind
  early at physical leaves and synthesis boundaries, late in between,
  with intent stated at the root of each scheduling scope — the
  assembly-time binding the language never offered. (§9)

## 2. Motivation

Three pressures, one missing abstraction.

**The zoo.** PipelineFIFO and BypassFIFO are one functional component
at two ordering points. The blocking FIFO is a third. `mkCReg`'s port
indices are hand-assigned positions; CRegN5/CRegA5/CRegUN5 are
hand-written Verilog at a magic five-port limit; BypassWire, DWire,
RWire are more points of the same family. Every one of these is the
ordering-space of a single functional design enumerated by hand,
because ordering contracts today bind at module-definition time. The
community's `mkFIFO`-as-parameter idiom is designers rediscovering the
missing late binding manually.

**Fighting the scheduler.** Inference's objective is maximize firing,
with arbitrary tie-breaks. That produces two distinct unpredictability
axes: *runtime arbitration coupling* — rule 3's firing modulates the
rule-1/rule-2 winner two hops up a WILL_FIRE chain no designer wrote —
and *design-evolution instability* — arbitrary tie-breaks are
sensitive to unrelated edits, so a distant change reshapes local
arbitration. Attributes exist to fight this, but they are pragmas: a
bag of stringly hints, expanded quadratically (§8), not a value
anyone can inspect, compose, or check.

**Boundaries.** Separate compilation (the artifact-graph RFC's
program) needs schedule facts to cross module boundaries. Exporting
them as relation matrices costs Θ((methods × levels)²) and inflates
precisely when implementations get more general. The contract needs a
representation that is linear in the interface and lets the parent
derive only the pairs it consumes. (§6)

## 3. The lattice

Per method pair, relations order by permissiveness: CF above the two
*incomparable* SB orderings above C — a diamond — extended pointwise
to matrices. Then:

- The **precise** schedule of an implementation is its principal
  schedule; bsc's scheduler already infers it.
- A **declared** schedule is an ascription, checked by **subsumption**
  (the post-GenWrap design's verify mode is literally this check).
  Weakening is upcast; conformance ⊑ is subtyping.
- **The subsumption lemma**: a parent correct against schedule s
  remains correct against any s′ ⊒ s. Substitutability is monotone;
  the parent's *optimal* schedule may improve under a more permissive
  child, but that is a recompile-for-optimization choice, never a
  correctness one — combined-vs-separate compilation, restated in
  lattice vocabulary.
- **Schedule variables** quantify with lattice bounds exactly as type
  variables do. A family contract is `fifoFamily :: SchedPoint →
  IfcContract (FIFOF t)`; schedule parameters join type variables and
  dictionary hashes in the telescope and the specialization key, and
  as specified binders are visibly applicable (`mkFIFO @Pipeline`).
- Two inference directions complete the picture: the **principal
  offer** (an implementation's precise schedule — exists today) and
  the **principal requirement** — the *weakest* child schedule under
  which a parent's rules still schedule, inferable from the parent's
  own uses. A schedule-polymorphic parent compiles to a constraint;
  binding is the constraint check.
- The canonical family: BypassFIFO and PipelineFIFO sit at the two
  incomparable SB points; the blocking FIFO (enq or deq, never both)
  is their **meet**; a dual-ported CF FIFO is the **join**. A parent
  declaring blocking works with all of them; one needing same-cycle
  enq+deq must say which ordering — which *is* the pipeline/bypass
  distinction, made precise.

Precedent: effect systems. Schedules are effects; this is row/effect
polymorphism with principal effect inference. Order-as-interface is
the session/behavioral-types line.

## 4. Positions: the type-side mechanism

The lattice says *what* schedules are; positions say *how* they enter
the type system, riding machinery bsc has had from birth.

**A fourth base kind.** bsc's kinds are literally `KStar | KNum |
KStr` (CType.hs:150) — KStr proves the base kinds are extensible — and
the typechecker already discharges provisos with an SMT backend
(`solvePred` inside TCMisc's `satisfy`, TCMisc.hs:649). Add a kind for
intra-cycle position, with **relational provisos only** — `Before# p q`
and kin — and deliberately **no literals and no arithmetic**. Integer
positions would recreate hand-assigned EHR indices; concrete positions
are solver *output*, never source. (This no-literals rule is one of
the two design points most worth external challenge — see §12.)

**Solving is cheap by construction.** Order constraints solve by
cycle-check plus topological sort — near-linear. The problem is
NP-hard only if you *optimize* when over-constrained; so don't:
over-constrained is an **error**, the type-error discipline applied to
schedules. The designer relaxes a constraint; the compiler never
searches.

**The witness is hardware.** The type-class analogy is exact:
discharging a proviso elaborates a dictionary; discharging
`Before# enq deq` (an enq-before-deq resolution) elaborates a bypass
network. Different relation axes have different witness families —
§10.

**Methods and rules unify.** A method's positions bind through its
callers; a rule is an anonymous method at a solver-assigned position —
unifying rule and method scheduling in the language the way ASchedule
already unifies them internally. Module-internal rules are
*existential* positions, constrained relative to the interface's
positions (the canonicalize-rule pattern).

**Where positions live in the type architecture:** position provisos
ride the CType phase index (artifact-graph RFC §6, v0.17): position
*variables* are inference-form citizens; saved signatures carry
solved, interned constraint sets — never concrete indices.

## 5. Schedules as values — and the unification

Contracts-as-values implies schedules-as-values: a contract *contains*
a scheduling component, and Clock and Reset already model the
endpoint — module parameters and ascriptions with deferred
realization. The pragma surface (`descending_urgency`,
`execution_order`, `preempts`, `mutually_exclusive`, `conflict_free`)
demotes to **constructors of a typed Schedule value**, validated at
construction — with the urgency constructors deleted per §5.b's
one-order ruling. The `-sched-dynamic` SchedAlt machinery is
runtime-*selected* schedule values already shipped in the trs
composition artifact; the static story is one more constructor, and
the dynamic engine an evaluation strategy over schedule values.

**The unification (the two arcs meeting):**

> A Schedule **value** is a **binding of position variables**.

The type side (§4) introduces the variables and the constraints; the
value side binds them. The **fill/verify dial** is then one question —
*how much of the solver's model does the designer pin?*

- **None**: today's full inference. The solver owns the model.
- **Partial**: constraints — pragmas made principled; the solver
  completes them (principal completion).
- **Total**: Kôika mode — a complete binding, cycle-accurate control,
  *verified legal* rather than inferred. The precedent is Kôika
  (Bourgeat, Pit-Claudel, Chlipala, Arvind — "The Essence of
  Bluespec", PLDI 2020): rules plus an explicit schedule object,
  one-rule-at-a-time semantics proved for *every* schedule, and
  performance tuning by changing the schedule value while rules stay
  untouched.

Values are what elaboration manipulates, serializes into contracts,
and hashes into specialization keys; types are what the checker
verifies and the solver completes. Same object, two faces — exactly
the contract/value story of the artifact-graph RFC, applied to
scheduling.

### 5.b One order: the urgency/execution distinction is dropped

bsc today maintains two orders per cycle — **urgency** (who wins
arbitration when conflicting rules contend) and **execution** (logical
position in the one-rule-at-a-time semantics) — and they may disagree
per pair: rule A can win arbitration over B while B executes earlier
when both fire. The freedom exists to scrape concurrency out of edge
cases, and it is a durable source of user confusion: two attribute
families, two mental models, and an amplifier for §2's compound
unpredictability.

**Ruling (Ravi, 2026-08-23): the new model has one order.** Positions
are it. Arbitration is positional — the sequential semantics runs
positions in order, and a later action that cannot legally extend the
cycle's history (a genuine conflict) does not fire. This is Kôika's
discipline exactly: it has no urgency axis at all, and its
every-schedule theorem never missed one. Note that value-overriding —
a later write superseding an earlier one through an EHR — is not
arbitration; it is sequential *composition*, which already favors
later positions. The two conventions (earlier wins the right to fire;
later wins the value) are consistent, not in tension: both are just
"run the order forward."

**"If you want the fancier arbitration, just write it down."** The
expressiveness lost is the *implicit* kind only. A pair that needs
B-before-A dataflow *and* A-beats-B arbitration on some third
resource remains expressible — as an explicit guard or an arbiter the
designer writes: stated intent (§8), not scheduler cleverness.
Consequences through the design:

- The Schedule value loses its urgency constructors.
  `descending_urgency` migrates as positional priority
  (earlier-listed = earlier-positioned); `preempts` survives on the
  co-firing axis (a directed must-not-co-fire plus a position fact).
- §6's two-axis relation domain is untouched — ordering and co-firing
  were never the urgency split; arbitration simply collapses into the
  ordering axis.
- The solver produces **one model per cycle**: no urgency/earliness
  merge, no reconciliation pass between two orders. The footprint
  schema carries one position field serving both consumers.
- §2's runtime-arbitration-coupling axis loses its amplifier — the
  worst coupling chains ran through the divergence.

**The loss is measurable, not asserted.** The divergence is statically
visible today: the scheduler can flag every pair whose final urgency
order differs from its final execution order. Running that census over
the testsuite and a large private corpus turns "the loss is
negligible" into a number — and names exactly the designs that need an
explicit-arbiter rewrite under migration.

## 6. Footprints: the contract representation

The pairwise matrix is the wrong export. Rule-pair relations are
unions of **complete bipartite blocks** indexed by (instance,
method-pair) SchedInfo classes — so the linear-size object is the
**footprint**: which regions (instances) a rule or method touches,
how, and at which positions. Every pairwise relation is a **derived
view** of two footprints. `SchedInfo` (SchedInfo.hs:33) is the
fully-monomorphized, fully-materialized degenerate case of this
contract; PR 47's inverted instance-to-users index is the first
factored artifact of the same decomposition.

Consequences:

- **Graph algorithms run on supernode encodings** — k₁+k₂ edges per
  bipartite block, not k₁·k₂; uniform per-resource relations check in
  O(k log k) and arbitrate in O(k) hardware.
- **Boundary contracts deflate.** Exporting EHR-generality as a
  relation matrix costs Θ((methods × levels)²); exporting footprints
  costs linear, and the parent derives only the pairs it actually
  needs.
- **Persist generators, not views.** The .ba should carry footprints;
  materialized pairwise databases are cache poison (the RuleRelationDB
  forcing measurement — an 18× residency jump on both compilers — is
  the direct evidence).
- **Vocabulary**: deriving SchedInfo from rule bodies *is* effect
  inference with regions = instances. The relation domain has two
  axes — admissible-order subsets over {before, after} for ordering,
  and may/must/must-not for co-firing — and the axes have different
  elaboration witnesses (§10).

## 7. The register under a total order: the EHR dissolves

The free object of this theory is the **position-polymorphic
register**: `read@p` / `write@p` with the EHR laws as axioms — a read
at position p observes the youngest write at any position before p,
else the flop; the last write commits at the edge. The EHR is this
object's shadow in a monomorphic language: port arity is just the
number of positions the ambient schedule distinguishes; the forwarding
mux chain is derived realization with priority literally the schedule
order; `mkCReg n` demotes to a derived form (a register plus n fresh
ascribed positions in the canonical CReg order), surface unchanged.

**The lattice placement** (from the value-side arc): precise = the
register under the total schedule — the denotation; declared = the
EHR — an ascription that positions p < q exist with observation
semantics, made without totalizing the ambient schedule. The EHR is to
the schedule what a type ascription is to inference, and it earns
*entity* status exactly at module boundaries — a register whose
observation points are exported is the boundary packaging of
(register + position bundle). Boundaries are **generalization
points**: composition means the parent's schedule linearly extends the
child's exported position order (today's
execution-order-of-separately-synthesized-submodule error family,
made compositional). `RevertingVirtualReg` dissolves entirely — a
schedule ascription wearing a module costume — as do the RWires
AAddSchedAssumps inserts.

**The worked example, carried to completion** (type-side arc): ONE
polymorphic FIFO text over position-polymorphic registers yields —
purely by constraint resolution —

- **pipeline** (deq before enq: flag path only),
- **bypass** (enq before deq: data mux elaborated as the `Before#`
  witness),
- **CF** (the capacity-1 resolution *derives* never-co-fire — the folk
  fact about one-element conflict-free FIFOs falls out of the
  constraints).

Rigid physical leaves are simply **position-monomorphic** — a BRAM
port sits at a fixed position — so an unimplementable resolution
surfaces as a *missing instance*: "no bypass on a BRAM-backed FIFO"
becomes a local elaboration error naming the constraint, instead of a
global scheduling surprise.

**Feasibility is not aspirational.** bsc already lives in the
total-order world internally: the composition artifact stores
`asch_rev_exec_order :: [ARuleId]` (ASyntax.hs:383) — a total linear
execution order per module — and bsc *totalizes even pairs the
semantics leaves free* (CF/ME rules get `CArbitraryChoice` execution
edges, ASchedule.hs:1558). Bluesim executes that order one rule at a
time; `-show-schedule` prints it as "Logical execution order"
(ADumpSchedule.hs:305). The order exists as an opaque scheduler
*output*; this RFC makes it a typed, valued, contract-crossing object.
Verilog says the same from outside: blocking-assignment order is a
total schedule spelled textually, so Verilog never needed an EHR
cell — the EHR is the price Bluespec paid for leaving intra-cycle
order implicit, and this design refunds it.

What survives as genuine element axes: persistence (with reset and
initialization — a wire is the degenerate register whose commit is
snipped) and unset-read behavior. Sequencing was never the element's
property.

## 8. What specification buys — and what it does not

The enumeration-vs-proof decomposition (type-side arc; the answer to
"is the Θ(n²) avoidable if the schedule were specified?"):

- **Choosing an order was never the cost.** Flattening is
  near-linear. The cost is computing and *checking* relation edges —
  identical work whether the schedule is inferred or specified — and
  edges exist only between rules sharing state (plus a
  foreign-function pseudo-resource).
- **Specification buys no asymptotics.** Verified concretely: bsc
  expands total `execution_order` / `descending_urgency` attributes
  into Θ(k²) pairwise edges *on top of* full inference
  (`extractSCConflictEdgesSP`, ASchedule.hs:2607;
  `extractUrgencyEdgesSP`, ASchedule.hs:1276 — and urgency edges are
  filtered against the computed conflict map, so the maps must exist
  anyway).
- **The implementation buys everything** — the resource-indexed
  transpose (PR 47, landed): bit-identical output, measured 25× at
  16k rules, fitted exponent 2.05 → ~1.6.
- What specification *genuinely* buys: (i) SMT exclusion proofs demote
  to **assertions** — ME/CF trusted and runtime-checked, the tedious
  per-pair residue eliminated; and (ii) — the deeper point — the
  **objective** changes: maximize-firing is replaced by *stated
  intent*. Concurrency becomes a stated requirement
  (must-fire-together, `fire_when_enabled`, always-before), and
  unstated freedom defaults to the *simplest stable* hardware, not the
  cleverest. This is the principled exit from both unpredictability
  axes of §2.

## 9. Binding time

Ordering contracts today bind at **module-definition time** (leaf
primitives; the zoo) or at **compile time** (inference's arbitrary
ties). The designer's knowledge lives at **assembly time** — the
binding time the language does not offer, which the
`mkFIFO`-as-parameter idiom approximates by hand.

The endpoint, consistent with the artifact-graph RFC's boundary
discipline:

- **Early-bound** at physical leaves and synthesis boundaries —
  contract compression (the Θ((m×L)²) point of §6 is exactly why
  boundaries want bound, compact contracts).
- **Late-bound** in between — schedule-polymorphic sources, positions
  as variables.
- **Intent stated at the root of each scheduling scope.**
- The gradient as workflow: *infer freely → surface the choices made →
  ratify them into pinned partial specs — a **schedule lockfile** —
  → feed solved orders into primitive selection.* The last step is
  Rosenband's compilation, restated.

Schedule bindings join the specialization key (with type
instantiations and dictionary hashes), so instance-specific synthesis
covers scheduling for free: `mkFIFO @Pipeline` and `mkFIFO @Bypass`
are two cache keys over one source.

## 10. Realization

Two orthogonal dials govern lowering:

- **Fill** (none / partial / total — §5) — how much of the model the
  designer pins.
- **Enables** (static / data-dependent) — Kôika's
  every-schedule theorem is bought with dynamic aborts compiled into
  data-dependent enable logic, strictly more permissive than static
  CF/SB relations at logic cost. Kôika mode = (total, data-dependent);
  classic bsc = (inferred-total, static); AAddSchedAssumps — which
  already inserts RWire-based dynamic assumption checks — is the
  embryo of a per-region middle.

Witnesses attach per relation axis (§6): the *ordering* axis
elaborates datapath witnesses (bypass vs registered paths); the
*co-firing* axis elaborates control witnesses (shared enables,
suppression). Derived forwarding then meets the artifact-graph RFC's
realization strategies: **structural** (flops plus derived mux chains —
EHR-shaped netlists, licenses discharged by construction) or **macro**
(position-monomorphic hard cells — BRAM write-modes, latch arrays —
whose schedule facts become carried external constraint obligations;
BRAM1.v's hand-encoded write-first behavior is the in-tree miniature).
Realization is per-instance — one source register realizes differently
under different bindings — which makes the specialization machinery
load-bearing for internal state, and extends "port names stop being
API" (A20) to internal nets: witnessed renderings apply there too.

## 11. Costs, honestly

1. **Coordinate assignment is the scheduling problem.** Where
   ascriptions are absent, placing operations on positions to satisfy
   contracts is Rosenband's performance-driven scheduling; principal
   schedule inference is the research core, and everything else here
   is downstream of it.
2. **Over-constrained means error, never search.** The NP-hardness
   fence (§4) is a usability bet: designers accept "relax one of these
   constraints" the way they accept type errors. If they don't, the
   pressure to optimize returns and the near-linear story breaks.
3. **Indexed state.** A register file observed at many positions
   derives address-compare bypass networks — processor forwarding
   written by the compiler. Power and cost at once; v1 scopes derived
   forwarding to scalar registers.
4. **Migration is compatibility-critical.** mkCReg, the pragma bag,
   and the FIFO zoo must demote to derived forms with unchanged
   surfaces (the zoo becomes one text plus frozen indices) — any
   step that breaks existing designs dies on arrival. The one
   deliberate break is §5.b's: designs exercising the
   urgency/execution divergence need explicit-arbiter rewrites, and
   the census names them in advance.

## 12. External challenge points

Flagged by the type-side arc as the two decisions most worth
adversarial review:

- **The no-literals rule.** Solver-owned models keep positions
  canonical and portable; designer-pinned indices (the EHR habit) are
  familiar and locally predictable. Is a total ban on position
  literals right, or does a disciplined pinning form (ascription-only,
  never arithmetic) earn its place?
- **Position-variable rigidity across scheduling scopes.** Clock
  domains and synthesis boundaries need region-like scoping of
  position variables — the scope structure (one solver model per
  domain per cycle, generalization at boundaries) needs a worked
  design, especially where domains interact through synchronizers.

## 13. Migration order

1. **Footprint artifact**: persist generators, not views — the .ba
   carries footprints; pairwise databases become derived caches
   (PR 47's inverted index is the first factored artifact; the
   RuleRelationDB residency evidence is the forcing function).
2. **Schedule value type**: the pragma surface demotes to
   constructors, validated at construction; no semantic change. The
   §5.b urgency-divergence census runs here — today's scheduler, zero
   new machinery — to size the one-order migration set with a number.
3. **Verify mode**: declared schedules checked by subsumption (the
   post-GenWrap verify mode, shipped for schedules).
4. **Position kind + relational provisos** behind a flag; method
   positions bind through callers; internal rules existential.
5. **Position-polymorphic registers** with derived structural
   forwarding, scalar only; the CReg surface demotes to a derived
   form.
6. **The FIFO demonstration**: one polymorphic text replaces the zoo,
   with the zoo's names as frozen-index compatibility shims;
   capacity-1-derives-CF as the acceptance test.
7. **Assembly-time binding surface** + the schedule lockfile workflow.
8. **Kôika mode**: total bindings verified legal; data-dependent
   enables per region as an opt-in.

Steps 1–3 are independently shippable and useful; 4 is the language
commitment; 5–6 are the payoff demonstration; 7–8 are the endgame.

## 14. Relation to prior work

- **RFC-bsc-artifact-graph.md** (same branch): §§14/14.b/14.c are this
  document's value-side ancestor and remain as its summary; §6
  (vocabulary-as-API, the CType phase index, interned serialization)
  supplies the type architecture positions ride on; §§9/13 supply
  specialization keys and the frozen/manifest machinery schedule
  bindings join; §10 supplies the realization split §10 here builds
  on.
- **The scheduling-complexity session** (type side; KB-recorded
  2026-08-23): enumeration-vs-proof, footprints, position-as-a-kind,
  EHR-as-free-object, binding-time framing — adopted here with its
  own challenge points preserved (§12). Companion implementation:
  MatX-inc bsc PR 47.
- **The post-GenWrap design** (July 2026, claude/model-rqj7c1): the
  verify mode (= subsumption checking), A20, licenses, witnesses.
- **Kôika** (PLDI 2020): schedules as syntactic objects, ORAAT for
  every schedule, dynamic aborts, the verified compiler.
- **Rosenband**: the EHR (MEMOCODE 2004) and performance-specification
  scheduling (with Arvind) — the coordinate-assignment core.
- **Effect systems / session types**: principal effects, rows,
  order-as-interface.
- **Verilog blocking assignment**: textual total schedules; the
  synthesizer derives forwarding — the existence proof that ordinary
  RTL designers already work under a total order without naming it.

## 15. Open questions

- Position scoping across clock domains and synthesis boundaries
  (§12): region system, one model per domain, generalization at
  boundaries; synchronizers as the inter-region morphisms?
- Asserted positions at foreign boundaries: what does `import "BVI"`
  ascribe — positions, footprints, or bare pairwise relations — and
  what does the conformance check demand of each?
- Footprint redaction: how much does a redacted boundary contract
  reveal (region names? counts?), and what does the parent lose in
  derivable pairs?
- Dynamic schedules: SchedAlt as *guarded position bindings* — is a
  runtime-selected binding a value-level case expression over
  schedule values, and what does the footprint of a dynamic module
  export?
- Whether `Pred`/`Scheme`/`Qual` carry position provisos through the
  CType phase index unchanged, or positions want their own constraint
  syntax class.
- The typechecker substitution remedy (union-find binding forest)
  interaction: position variables join the same forest or get a
  dedicated near-linear order-solver state?
- How footprints compose through vseg/vlink: does the link-time
  constraint composition (artifact-graph §10) carry footprint
  obligations the same way it carries macro constraint obligations?
