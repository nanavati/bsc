package TickerIfc;

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
module mkTickerA(Ticker);
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

endpackage
