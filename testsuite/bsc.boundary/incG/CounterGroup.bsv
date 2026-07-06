// Increment G: a mixed implementation group -- generated always_ready
// members plus a ready-less BVI member -- formed with mkOneOf.
//
// Every member was checked against contract_Counter at its own
// compile (the generated ones at codegen, the BVI at CounterImport's
// package compile); the group site only seals the root's boundary at
// the declaration and records the alternates (pinout equality).
//
// Selection is observable: root counts by 1, "two" by 2, "vlog"
// (the hand-written counterV.v, module mkCounterV) by 3.

package CounterGroup;

import List::*;
import CounterIfc::*;
import CounterImport::*;

(* synthesize, always_ready *)
module mkCounterUp(Counter);
   Reg#(Bit#(8)) c <- mkReg(0);

   method Bit#(8) value();
      return c;
   endmethod
   method Action incr();
      c <= c + 1;
   endmethod
endmodule

(* synthesize, always_ready *)
module mkCounterTwo(Counter);
   Reg#(Bit#(8)) c <- mkReg(0);

   method Bit#(8) value();
      return c;
   endmethod
   method Action incr();
      c <= c + 2;
   endmethod
endmodule

(* synthesize *)
module mkGroupTb(Empty);
   Counter c <- mkOneOf(cons(tuple2("two", mkCounterTwo),
                        cons(tuple2("vlog", mkCounterVlog), nil)),
                        mkCounterUp);
   Reg#(Bit#(8)) n <- mkReg(0);

   rule step;
      if (n < 4)
         c.incr();
      else begin
         $display("count=%0d", c.value());
         $finish(0);
      end
      n <= n + 1;
   endrule
endmodule

endpackage
