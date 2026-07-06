// NEGATIVE: the root of a group must be the boundary of a synthesized
// module instance; an inlined root's interface is built from inner
// state (here a register), which fails the boundary check instead of
// silently losing the group.

import List::*;
import CounterDefs::*;

// not marked (* synthesize *)
module mkCounterInline(Counter);
   Reg#(Bit#(8)) count <- mkReg(0);
   method Action incr();
      count <= count + 1;
   endmethod
   method Bit#(8) value();
      return count;
   endmethod
endmodule

(* synthesize *)
module mkTbGroupInlineRoot();
   Counter c <- mkOneOf(cons(tuple2("stub", mkCounterStub), nil),
                        mkCounterInline);
   rule show;
      $display("%0d", c.value());
      $finish(0);
   endrule
endmodule
