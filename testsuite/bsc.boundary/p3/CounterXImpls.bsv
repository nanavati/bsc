// Cross-package group, package 2 of 3: the members, compiled against
// the contract imported from CounterXIfc.

import CounterXIfc::*;

(* synthesize *)
module mkCounterX(CounterX);
   Reg#(Bit#(8)) count <- mkReg(0);
   method Action incr();
      count <= count + 1;
   endmethod
   method Bit#(8) value();
      return count;
   endmethod
endmodule

(* synthesize *)
module mkCounterXStub(CounterX);
   Reg#(Bit#(8)) count <- mkReg(0);
   method Action incr();
      count <= count + 1;
   endmethod
   method Bit#(8) value();
      return 0;
   endmethod
endmodule
