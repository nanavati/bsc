// Increment I, consumer side: a separately-compiled parent
// instantiates the contract-collapsed member through its .bo (the
// recorded boundary has no RDY_tick/RDY_count), calls the collapsed
// methods unguarded, and the guarded method normally.

package TbTicker;

import TickerIfc::*;

(* synthesize *)
module mkTbTicker();
   Ticker t <- mkTickerA;
   Reg#(Bit#(8)) n <- mkReg(0);

   rule step (n < 3);
      t.tick();
      n <= n + 1;
   endrule

   rule fin (n == 3);
      $display("count %0d", t.count());
      t.pause();
      $finish(0);
   endrule
endmodule

endpackage
