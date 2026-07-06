// Shadow check, vector-of-subinterface: Vector#(2, Sub) puts numeric
// components in the member paths (subs_0_get, subs_1_get, ...),
// exercising the checker's numeric-leaf traversal of the boundary_
// description.

package VecShadow;

import Vector::*;

interface Sub;
   method Action put(Bit#(8) x);
   method Bit#(8) get();
endinterface

interface VecIfc;
   interface Vector#(2, Sub) subs;
endinterface

(* synthesize *)
module mkVecShadow(VecIfc);
   Vector#(2, Reg#(Bit#(8))) rs <- replicateM(mkReg(0));

   Vector#(2, Sub) ss = newVector;
   for (Integer i = 0; i < 2; i = i + 1)
      ss[i] = (interface Sub;
                  method Action put(Bit#(8) x);
                     rs[i] <= x;
                  endmethod
                  method Bit#(8) get();
                     return rs[i];
                  endmethod
               endinterface);

   interface subs = ss;
endmodule

endpackage
