// Increment G negative: a DECLARED ready port contradicts
// contractAlwaysReady.  contract_Counter promises constant readiness
// for "value"; this import declares a ready clause for it, so its
// readiness is NOT promised constant and the boundary is rejected at
// this package's compile.

package CounterDeclaredReady;

import CounterIfc::*;

import "BVI" mkCounterRdyV = module mkCounterRdy(Counter);
   default_clock clk(CLK);
   default_reset rst(RST_N);
   method value value() ready(RDY_value);
   method incr() enable(EN_incr);
   schedule (value) CF (value);
   schedule (value) SB (incr);
   schedule (incr) C (incr);
endmodule

endpackage
