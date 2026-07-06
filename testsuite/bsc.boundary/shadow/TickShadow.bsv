// Shadow check, contractAlwaysReady collapse (modeled on
// incI/TickerIfc.bsv): tick/count are declared always-ready by the
// contract and lose their RDY twins at the member's own boundary;
// pause is undeclared and keeps RDY_pause.  The shadow must describe
// the EFFECTIVE (collapsed) boundary, not the pre-collapse one.  The
// Tb shows the flag does not perturb behavior.

package TickShadow;

import List::*;

interface Ticker;
   method Action tick();
   method Bit#(8) count();
   method Action pause();
endinterface

List#(ContractStmt) contract_Ticker =
   cons(contractSB("count", "tick"),
   cons(contractSB("count", "pause"),
   cons(contractAlwaysReady("tick"),
   cons(contractAlwaysReady("count"), nil))));

(* synthesize *)
module mkTickShadow(Ticker);
   Reg#(Bit#(8)) c <- mkReg(0);
   Reg#(Bool)    live <- mkReg(True);

   method Action tick();
      if (live)
         c <= c + 1;
   endmethod

   method Bit#(8) count();
      return c;
   endmethod

   method Action pause() if (live);
      live <= False;
   endmethod
endmodule

(* synthesize *)
module mkTickShadowTb();
   Ticker t <- mkTickShadow;
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
