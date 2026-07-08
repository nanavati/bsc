// Behavior under injection: drive the hierarchical DUT through the
// injected-skeleton-then-wrapper path and check the values.

import HierInj::*;

(* synthesize *)
module mkInjTb();
   HierIfc h <- mkHierInj;
   Reg#(Bit#(2)) st <- mkReg(0);

   rule go;
      st <= st + 1;
      case (st)
         0: h.sub.poke(42);
         1: begin
               $display("inj=%0d ready=%0d", h.sub.peek(),
                        pack(h.ready()));
               $finish(0);
            end
      endcase
   endrule
endmodule
