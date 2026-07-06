// Increment F negative: a malformed path in a convention atom is
// rejected with the MethodPath grammar error (reported against the
// convention def when the implementation is generated).

package ConvBadPath;

import List::*;

interface Sub;
   method Action put(Bit#(8) x);
endinterface

interface ConvBad;
   interface Sub sub;
endinterface

// malformed: empty path component ("sub..put")
List#(ConventionStmt) convention_ConvBad =
   cons(conventionReadyValid("sub..put"), nil);

(* synthesize *)
module mkConvBad(ConvBad);
   Reg#(Bit#(8)) v    <- mkReg(0);
   Reg#(Bool)    busy <- mkReg(False);

   rule drain (busy);
      busy <= False;
   endrule

   interface Sub sub;
      method Action put(Bit#(8) x) if (!busy);
         v <= x;
         busy <= True;
      endmethod
   endinterface
endmodule

endpackage
