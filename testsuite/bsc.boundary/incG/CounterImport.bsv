// Increment G: a conforming ready-less BVI import.
//
// The import "BVI" is a hand-declared boundary, so the same
// actual-refines-declared check applies at THIS package's compile
// (bviImportErrs runs post-fixupDefs): the declared VModInfo is
// checked against contract_Counter.
//
//  - no ready clauses: readiness constant, satisfying both
//    contractAlwaysReady atoms;
//  - the schedule clauses grant the declared SB("value", "incr").

package CounterImport;

import CounterIfc::*;

import "BVI" mkCounterV = module mkCounterVlog(Counter);
   default_clock clk(CLK);
   default_reset rst(RST_N);
   method value value();
   method incr() enable(EN_incr);
   schedule (value) CF (value);
   schedule (value) SB (incr);
   schedule (incr) C (incr);
endmodule

endpackage
