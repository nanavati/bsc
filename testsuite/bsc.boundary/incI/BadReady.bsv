// Increment I negative: the contract declares tick always-ready, but
// this member guards it, so its readiness is not provably constant --
// rejected at the member's own compile (the same proof obligation the
// always_ready pragma raises).

package BadReady;

import TickerIfc::*;

(* synthesize *)
module mkTickerBad(Ticker);
   Reg#(Bit#(8)) c <- mkReg(0);
   Reg#(Bool)    live <- mkReg(True);

   method Action tick() if (live);
      c <= c + 1;
   endmethod

   method Bit#(8) count();
      return c;
   endmethod

   method Action pause() if (live);
      live <= False;
   endmethod
endmodule

endpackage
