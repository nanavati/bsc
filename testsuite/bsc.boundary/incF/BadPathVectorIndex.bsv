// Increment F negative: vector-INDEX syntax ("fifo[0].get") is not a
// method path -- '[' and ']' are not identifier characters, so the
// atom fails the MethodPath grammar (MethodPath ::= ident ("." ident)*).
// (The canonical spelling of a vector element is the numeric
// component, "fifo.0.get", as the second atom argument shows.)

package BadPathVectorIndex;

import List::*;
import Vector::*;

interface Sub;
   method Action put(Bit#(8) x);
   method Bit#(8) get();
endinterface

interface Wrap;
   interface Vector#(2, Sub) fifo;
endinterface

List#(ContractStmt) contract_Wrap =
   List::cons(contractSB("fifo[0].get", "fifo.0.put"), List::nil);

(* synthesize *)
module mkBadPathVectorIndex(Wrap);
   Vector#(2, Reg#(Bit#(8))) rs <- replicateM(mkReg(0));

   Vector#(2, Sub) ss = newVector;
   for (Integer i = 0; i < 2; i = i + 1) begin
      ss[i] = (interface Sub;
                  method Action put(Bit#(8) x);
                     rs[i] <= x;
                  endmethod
                  method Bit#(8) get();
                     return rs[i];
                  endmethod
               endinterface);
   end

   interface fifo = ss;
endmodule

endpackage
