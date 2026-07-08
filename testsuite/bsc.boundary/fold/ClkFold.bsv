// Clock and Reset output fields: opaque entries in the description
// (native floor, no codec) which now carry the naming slots the
// fold's saveFieldPortTypes statements are rendered from.

import Clocks::*;

interface ClkIfc;
   interface Clock cout;
   interface Reset rout;
   method Bool val();
endinterface

(* synthesize *)
module mkClkFold(ClkIfc);
   Clock c <- exposeCurrentClock;
   Reset r <- exposeCurrentReset;
   Reg#(Bool) b <- mkReg(False);
   interface cout = c;
   interface rout = r;
   method val = b._read;
endmodule
