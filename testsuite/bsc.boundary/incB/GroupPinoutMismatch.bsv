// NEGATIVE: pinout equality is a mechanism precondition -- the
// emitted instantiation is reused verbatim -- so an alternate with an
// extra module argument (a port) is rejected at the group site.

import List::*;
import CounterSeal::*;

(* synthesize *)
module mkCounterStep#(Bit#(8) step)(Counter);
   Reg#(Bit#(8)) count <- mkReg(0);
   method Action incr();
      count <= count + step;
   endmethod
   method Bit#(8) value();
      return count;
   endmethod
endmodule

(* synthesize *)
module mkTbGroupPinout();
   Counter c <- mkOneOf(cons(tuple2("step", mkCounterStep(8'd2)), nil),
                        mkCounterTight);
   rule show;
      $display("%0d", c.value());
      $finish(0);
   endrule
endmodule
