// NEGATIVE: a boundary with port arguments cannot form a group; port
// arguments are interface arguments in degenerate form and their
// contracts are not yet expressible.

import List::*;
import CounterDefs::*;

(* synthesize *)
module mkCounterPort#(Bit#(8) start)(Counter);
   Reg#(Bit#(8)) count <- mkReg(0);
   method Action incr();
      count <= count + start;
   endmethod
   method Bit#(8) value();
      return count;
   endmethod
endmodule

(* synthesize *)
module mkTbGroupPortArg();
   Counter c <- mkOneOf(cons(tuple2("stub", mkCounterStub), nil),
                        mkCounterPort(8'd1));
   rule show;
      $display("%0d", c.value());
      $finish(0);
   endrule
endmodule
