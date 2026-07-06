# bsc.boundary/typed

Tests for the Prelude's typed layer over synthesized boundaries
(SynthPort/SynthMethod/SynthField, Synthesizable/synthShape,
MediateField, WrapIfc', genericWrapIfc/genericUnwrapIfc): round-trip
conversion between same-shaped interfaces (plain and mixed-field, both
backends), compile-only Clock/Reset mediation, negatives for non-Bits
leaves and boundary-shape mismatches, and a synthShape/messageM probe.
DRAFT: all expectations marked "# TOFREEZE" in typed.exp (and the
.out.expected files they compare against) are hand-computed and still
need freezing against live runs.
