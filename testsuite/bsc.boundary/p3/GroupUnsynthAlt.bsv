// NEGATIVE: alternates must be separately synthesized modules; an
// inlined (non-synthesized) alternate has no Verilog boundary to
// point the emitted selection at.

import List::*;
import CounterDefs::*;

// not marked (* synthesize *)
module mkCounterPure(Counter);
   method Action incr();
      noAction;
   endmethod
   method Bit#(8) value();
      return 0;
   endmethod
endmodule

(* synthesize *)
module mkTbGroupUnsynthAlt();
   Counter c <- mkOneOf(cons(tuple2("alt", mkCounterPure), nil),
                        mkCounterA);
   rule show;
      $display("%0d", c.value());
      $finish(0);
   endrule
endmodule
