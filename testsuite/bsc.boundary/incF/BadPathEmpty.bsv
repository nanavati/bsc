// Increment F negative: the empty string fails the MethodPath grammar
// (MethodPath ::= ident ("." ident)*).

package BadPathEmpty;

import List::*;

interface Sub;
   method Action put(Bit#(8) x);
   method Bit#(8) get();
endinterface

interface Wrap;
   interface Sub fifo;
endinterface

List#(ContractStmt) contract_Wrap =
   cons(contractAlwaysReady(""), nil);

(* synthesize *)
module mkBadPathEmpty(Wrap);
   Reg#(Bit#(8)) r <- mkReg(0);
   interface Sub fifo;
      method Action put(Bit#(8) x);
         r <= x;
      endmethod
      method Bit#(8) get();
         return r;
      endmethod
   endinterface
endmodule

endpackage
