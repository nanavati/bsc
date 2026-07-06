// Cross-package group, package 3 of 3: the group is formed in a
// package that imports the interface (and contract) from one package
// and the members from another.

import List::*;
import CounterXIfc::*;
import CounterXImpls::*;

(* synthesize *)
module mkTbCross();
   CounterX c <- mkOneOf(cons(tuple2("stub", mkCounterXStub), nil),
                         mkCounterX);
   Reg#(Bit#(8)) cycle <- mkReg(0);

   rule count_up (cycle < 5);
      c.incr();
   endrule

   rule step;
      cycle <= cycle + 1;
      if (cycle == 6) begin
         $display("final value %0d", c.value());
         $finish(0);
      end
   endrule
endmodule
