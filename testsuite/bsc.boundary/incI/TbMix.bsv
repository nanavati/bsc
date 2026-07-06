// Increment I mixed group: pragma-free contract-collapsed generated
// root + ready-less BVI alternate.  Pinout equality holds because the
// contract collapsed the root's RDY ports.

package TbMix;

import List::*;
import MixIfc::*;

(* synthesize *)
module mkTbMix();
   Counter c <- mkOneOf(cons(tuple2("vlog", mkCounterVlog), nil),
                        mkCounterUp);
   Reg#(Bit#(8)) n <- mkReg(0);

   rule up (n < 4);
      c.incr();
      n <= n + 1;
   endrule

   rule fin (n == 4);
      $display("value %0d", c.value());
      $finish(0);
   endrule
endmodule

endpackage
