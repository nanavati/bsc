package ScanTb;

import List::*;
import ScanDefs::*;

(* synthesize *)
module mkScanTb();
   // instantiate the decoy so its signature def is in play
   Pulse_AB d <- mkPulseABImpl;
   Pulse p <- mkOneOf(cons(tuple2("stub", mkPulseARStub), nil), mkPulseAR);
   Reg#(Bit#(8)) n <- mkReg(0);
   rule go (n < 3);
      p.tick();
      n <= n + 1;
   endrule
   rule fin (n == 3);
      $display("cnt %0d d %0d", p.cnt(), d.x());
      $finish(0);
   endrule
endmodule

endpackage
