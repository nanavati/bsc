// always_ready on the interface declaration: GenWrap mints the
// AR_-prefixed flat type, the boundary drops every RDY port, and the
// description (emitted for the minted type) must still drive the
// fold.

(* always_ready *)
interface ArIfc;
   method Bit#(4) count();
   method Action bump();
endinterface

(* synthesize *)
module mkArFold(ArIfc);
   Reg#(Bit#(4)) c <- mkReg(0);
   method count = c._read;
   method Action bump();
      c <= c + 1;
   endmethod
endmodule
