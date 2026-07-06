// A synthesized parent forming an implementation group over
// mkCounterA, with mkCounterStub as a selectable alternate.
//
// Default selection counts to 5; selecting "stub" (Verilog
// -DBSV_IMPL_..., Bluesim -use-impl) leaves value stuck at 0.
// The $display fires exactly once, so the output is deterministic.

import List::*;
import CounterDefs::*;

(* synthesize *)
module mkTbGroupSelect();
   Counter c <- mkOneOf(cons(tuple2("stub", mkCounterStub), nil), mkCounterA);

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
