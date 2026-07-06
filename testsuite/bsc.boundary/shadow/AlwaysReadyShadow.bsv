// Shadow check, always_ready pragma: the RDY twins are absent from
// the assembled boundary AND from the shadow's view of it -- the
// checker must not demand RDY members the pragma removed.

package AlwaysReadyShadow;

interface ARIfc;
   method Action poke(Bit#(8) x);
   method Bit#(8) peek();
endinterface

(* synthesize, always_ready *)
module mkAlwaysReadyShadow(ARIfc);
   Reg#(Bit#(8)) r <- mkReg(0);

   method Action poke(Bit#(8) x);
      r <= x;
   endmethod

   method Bit#(8) peek();
      return r;
   endmethod
endmodule

endpackage
