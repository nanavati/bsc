# incE: retractable ready/valid at the Verilog boundary (A91/A99)

Behavioral tests for the exported ready/valid convention: a method
tagged `conventionReadyValid` accepts a request (EN) asserted while
not ready, and the transfer happens on request AND ready
(`AAddScheduleDefs.gateRV` gates the method's execute condition with
its own RDY).

Files:

- `StreamRV.bsv` — stream producer `mkRVStream` whose Action method
  `deq` is tagged `conventionReadyValid` and is ready one cycle in
  four (guard `ph == 0`); the generated `.v` shows the gate:
  `data$EN = EN_deq && ph == 2'd0`.
- `tbRVGarbage.v` — the headline test: a hand-written Verilog master
  that ties `EN_deq` high on every cycle (garbage requests during
  not-ready periods), `$display`s the observed `RDY_deq`/`first`
  sequence, and prints a FAIL line if state moves on a not-ready
  request or holds on a ready one.  Linked with the producer via
  `link_verilog_pass` and compared to `tbRVGarbage.out.expected`:
  state advances exactly once per ready cycle.
- `TbRVConsumer.bsv` — the consumer side untouched: a classic BSV
  parent calls `deq` under its implicit condition (EN implies ready),
  so the gate is a no-op for a well-behaved caller.  Compiled, linked
  and simulated on both backends (Bluesim cannot drive garbage
  requests; it checks the gated package compiles and runs) against
  `sysERVConsumer.out.expected`.

All expected outputs were frozen against a live run of this tree's
compiler with iverilog.
