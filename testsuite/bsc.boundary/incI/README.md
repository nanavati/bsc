Increment I: `contractAlwaysReady` collapses the RDY port.

A member whose interface contract declares methods always-ready gets
those RDY ports removed from its Verilog boundary at its own compile
(no `always_ready` pragma anywhere); undeclared guarded methods keep
theirs.  A separately-compiled parent consumes the collapsed boundary
through the .bo on both backends.  A member that guards a declared
method is rejected with the always-ready proof (G0006).  A pragma-free
generated root forms a group with a ready-less BVI (pinouts equal
post-collapse), selected under both macros and default.
