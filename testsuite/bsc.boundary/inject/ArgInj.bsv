// Module arguments under injection: a parameter, a dynamic port,
// and a vector argument (port-exploded to k_0/k_1) all flow through
// the recorded argument info (bs_vtis/bs_argpts) into the
// genModule-time skeleton.

import Vector::*;

interface ArgIfc;
   method Bit#(8) out();
endinterface

(* synthesize *)
module mkArgInj#(parameter Bit#(4) p, Bit#(8) d,
                 Vector#(2, Bit#(8)) k)(ArgIfc);
   Reg#(Bit#(8)) r <- mkReg(0);

   rule acc;
      r <= r + d + k[0] + k[1] + zeroExtend(p);
   endrule

   method out = r._read;
endmodule
