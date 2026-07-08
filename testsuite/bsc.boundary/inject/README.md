# The injection relocation, pilot (increment 11)

Under the hidden `-boundary-inject` flag, GenWrap stops planting the
wrapper skeleton in the package.  Today's pre-typecheck rewrite
demotes the user's module to a `let`-binding inside a generated
`<mod>_` skeleton (renamed with the gen suffix, its type
monomorphized); under injection the user's def stays a **top-level
def, unrenamed and unstubbed**, typechecked as written, and the
skeleton is constructed at `genModule` time from the recorded
`BoundarySpec` (module argument info and port-type mapping recorded
at GenWrap time) and compiled by the same per-module pipeline that
already compiles the final wrapper (`compileCDefToIDef`).  The
synthesis-order graph treats the intact user def as its node.

This is the first slice of the design doc's section-5.3 relocation:
the invasive half of the rewrite (rename + demotion + skeleton) is
gone from the package; the additive half (flat interface types,
`to_`/`from_`, `Generic` instances, description defs) still runs and
is scheduled to move in later increments.

Tests: census assertions via `BSC_BOUNDARY_INJECT_LOG` (`inject
<mod>` per generated module, no `legacy`), boundary port names for a
prefixed subinterface and for parameter/port/vector-exploded module
arguments, a user error whose reporting phase moves to genModule but
whose message survives (`BadArgInj`), composition with
`-boundary-fold -check-wrap-shadow`, and Bluesim behavior through
the injected path.  Byte-identity of generated Verilog flag-on vs
flag-off is gated by the corpus comparison outside this suite.
