`-check-wrap-shadow`: at every module generation the compiler replays
the GenWrap-emitted `boundary_<flatifc>` description against the
assembled boundary (member names incl. RDY twins after any
contractAlwaysReady collapse, clocks/resets/inouts, per-kind port
shape); disagreement is S0015.  All positives -- a mismatch requires a
compiler bug -- so every source also compiles flag-off for baseline.
