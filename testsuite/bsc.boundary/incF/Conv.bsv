// Increment F (A97): dotted method paths in CONVENTION atoms.
//
// convention_<Ifc> accepts the same MethodPath grammar as contracts:
// conventionReadyValid("sub.put") names a sub-interface method, and
// is flattened to the boundary name "sub_put" when the retractable
// ready/valid realization is applied.

package Conv;

import List::*;

interface Sub;
   method Action put(Bit#(8) x);
endinterface

interface ConvOuter;
   interface Sub sub;
endinterface

// dotted path in a convention atom
List#(ConventionStmt) convention_ConvOuter =
   cons(conventionReadyValid("sub.put"), nil);

(* synthesize *)
module mkConvOuter(ConvOuter);
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
