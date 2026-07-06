// NEGATIVE: a module whose inferred schedule violates the declared
// contract.  contract_Counter declares value SB incr, but here value
// reads a wire written by incr, so the module cannot schedule value
// before incr; the error is positioned at the module and names the
// declared relation.

import List::*;
import CounterDefs::*;

(* synthesize *)
module mkCounterBad(Counter);
   Reg#(Bit#(8)) count <- mkReg(0);
   RWire#(Bit#(8)) bypass <- mkRWire;

   method Action incr();
      count <= count + 1;
      bypass.wset(count + 1);
   endmethod

   method Bit#(8) value();
      return fromMaybe(count, bypass.wget());
   endmethod
endmodule
