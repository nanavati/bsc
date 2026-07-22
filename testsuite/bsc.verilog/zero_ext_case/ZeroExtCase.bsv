// A case whose selector is a constant-zero extension.  The index is two
// bits widened to three, so half the arms of the padded width can never
// match.
import Vector::*;

(* synthesize *)
module mkZeroExtCase (Empty);
   Vector#(8, Reg#(Bit#(8))) v <- replicateM(mkReg(0));
   Reg#(Bit#(2)) idx <- mkReg(0);
   Reg#(Bit#(8)) out <- mkReg(0);

   rule go;
      out <= v[{1'b0, idx}];
   endrule
endmodule
