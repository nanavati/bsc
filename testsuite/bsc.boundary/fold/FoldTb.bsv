// Behavior under the fold: drive the hierarchical and vector DUTs
// through their folded wrappers and check the values that come back.

import Vector::*;
import HierFold::*;
import VecFold::*;

(* synthesize *)
module mkFoldTb();
   HierIfc h <- mkHierFold;
   VecIfc v <- mkVecFold;
   Reg#(Bit#(3)) st <- mkReg(0);

   rule go;
      st <= st + 1;
      case (st)
         0: begin
               h.sub.poke(17);
               v.items[0].put(1);
            end
         1: begin
               v.items[1].put(2);
               v.items[2].put(3);
            end
         2: begin
               $display("hier=%0d ready=%0d", h.sub.peek(),
                        pack(h.ready()));
               $display("vec=%0d %0d %0d", v.items[0].get(),
                        v.items[1].get(), v.items[2].get());
               $finish(0);
            end
      endcase
   endrule
endmodule
