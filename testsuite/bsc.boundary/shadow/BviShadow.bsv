// Shadow check, BVI import: an imported module has no boundary_ def
// and no generated wrapper, so the check (which runs per GENERATED
// module) must not fire on the import itself.  mkBviUser is generated
// and instantiates the BVI; only mkBviUser's own boundary is checked.
// (BVI modeled on incI/MixIfc.bsv + counterV.v.)

package BviShadow;

interface Counter;
   method Action incr();
   method Bit#(8) value();
endinterface

import "BVI" mkCounterV = module mkCounterVlog(Counter);
   default_clock clk(CLK);
   default_reset rst(RST_N);
   method value value();
   method incr() enable(EN_incr);
   schedule (value) CF (value);
   schedule (value) SB (incr);
   schedule (incr) C (incr);
endmodule

(* synthesize *)
module mkBviUser(Counter);
   Counter inner <- mkCounterVlog;

   method Action incr();
      inner.incr();
   endmethod

   method Bit#(8) value();
      return inner.value();
   endmethod
endmodule

endpackage
