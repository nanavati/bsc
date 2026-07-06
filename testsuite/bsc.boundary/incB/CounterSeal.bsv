// The interface, its declared contract, and two conforming members
// whose own schedules differ: sealing must present the declaration,
// not a member's accidents, to the parent.

import List::*;

interface Counter;
   method Action incr();
   method Bit#(8) value();
endinterface

List#(ContractStmt) contract_Counter =
   cons(contractSB("value", "incr"),
   cons(contractAlwaysReady("value"), nil));

// value reads a register that incr never writes, so this member's
// inferred schedule has the extra freedom value CF incr (an accident
// the declaration does not promise)
(* synthesize *)
module mkCounterLoose(Counter);
   Reg#(Bit#(8)) count <- mkReg(0);
   Reg#(Bit#(8)) snap <- mkReg(0);
   method Action incr();
      count <= count + 1;
   endmethod
   method Bit#(8) value();
      return snap;
   endmethod
endmodule

// value reads the counted register: exactly the declared value SB incr
(* synthesize *)
module mkCounterTight(Counter);
   Reg#(Bit#(8)) count <- mkReg(0);
   method Action incr();
      count <= count + 1;
   endmethod
   method Bit#(8) value();
      return count;
   endmethod
endmodule
