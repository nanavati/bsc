// An Inout interface member: an opaque entry of kind "inout".

interface IoIfc;
   interface Inout#(Bit#(8)) io;
   method Bool valid();
endinterface

(* synthesize *)
module mkInoutFold#(Inout#(Bit#(8)) x)(IoIfc);
   Reg#(Bool) b <- mkReg(False);
   interface io = x;
   method valid = b._read;
endmodule
