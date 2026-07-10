# The injection relocation, pilot (increment 11)

Under the hidden `-boundary-inject` flag, the wrapper skeleton is no
longer package content.  It is still planted at GenWrap time exactly
as today (the discovery rounds showed each pipeline stage the
skeleton rides is load-bearing: typecheck renders user errors in
module argument types and marks imports used; the stub/body split
lets parents typecheck against the polymorphic stub while the body
forces `Module`; `iSimplify` deep-forces and so can run neither
before nor after a per-def re-knot), but its finished IDef is then
**captured and the def dropped from the package** before the
generation loop -- the `.bo` carries no skeleton -- and at its
module's `genModule` turn the captured IDef is re-knotted against
the current package (every same-package reference refreshed, so
sibling generated modules are seen post-synthesis at every depth;
positions untouched) and compiled by the same per-module pipeline
that already compiles the final wrapper (`compileCDefToIDef`).

This is the first slice of the design doc's section-5.3 relocation:
the wrapper definition is no longer parent-visible package content
beyond its stub, is absent from the `.bo`, and is constructed
per-generation; the additive half of the rewrite (flat interface
types, `to_`/`from_`, `Generic` instances, description defs) still
runs pre-typecheck and is scheduled to move in later increments.

Tests: census assertions via `BSC_BOUNDARY_INJECT_LOG` (`inject
<mod>` per generated module, no `legacy`), boundary port names for a
prefixed subinterface and for parameter/port/vector-exploded module
arguments, a same-package sibling instantiation whose skeleton
reaches the sibling only through the renamed user def
(`SiblingInj`; the generated-members-only re-knot spun the
evaluator forever on the stale pre-synthesis knot), a user error
whose reporting phase moves to genModule but whose message survives
(`BadArgInj`), composition with `-boundary-fold -check-wrap-shadow`,
and Bluesim behavior through the injected path.  Byte-identity of generated Verilog flag-on vs
flag-off is gated by the corpus comparison outside this suite.
