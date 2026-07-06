// Increment I, the mixed-group payoff: with contractAlwaysReady doing
// the collapse, a pragma-FREE generated member has the same pinout as
// a ready-less BVI, so they form a group with no always_ready pragma
// anywhere.  (Increment G needed the pragma on the generated root for
// the pinouts to match; the contract now carries that fact.)

package MixIfc;

import List::*;

interface Counter;
   method Action incr();
   method Bit#(8) value();
endinterface

List#(ContractStmt) contract_Counter =
   cons(contractSB("value", "incr"),
   cons(contractAlwaysReady("value"),
   cons(contractAlwaysReady("incr"), nil)));

(* synthesize *)
module mkCounterUp(Counter);
   Reg#(Bit#(8)) c <- mkReg(0);
   method Action incr();
      c <= c + 1;
   endmethod
   method Bit#(8) value();
      return c;
   endmethod
endmodule

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
