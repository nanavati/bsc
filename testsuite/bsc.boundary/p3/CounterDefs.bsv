// The shared interface, its declared contract, and the group members.
//
// The contract is declared beside the interface by naming convention
// (contract_<Ifc>), as a literal list of contract statements; every
// module implementing the interface is checked against it at its own
// compile.

import List::*;

interface Counter;
   method Action incr();
   method Bit#(8) value();
endinterface

List#(ContractStmt) contract_Counter =
   cons(contractSB("value", "incr"),
   cons(contractAlwaysReady("value"), nil));

// the default implementation: an ordinary counter
// (value reads before incr writes: value SB incr; value is always
// ready -- so it conforms to the declaration)
(* synthesize *)
module mkCounterA(Counter);
   Reg#(Bit#(8)) count <- mkReg(0);
   method Action incr();
      count <= count + 1;
   endmethod
   method Bit#(8) value();
      return count;
   endmethod
endmodule

// an alternate implementation with the same boundary: value is stuck
// at zero (observably different from mkCounterA in simulation)
(* synthesize *)
module mkCounterStub(Counter);
   Reg#(Bit#(8)) count <- mkReg(0);
   method Action incr();
      count <= count + 1;
   endmethod
   method Bit#(8) value();
      return 0;
   endmethod
endmodule
