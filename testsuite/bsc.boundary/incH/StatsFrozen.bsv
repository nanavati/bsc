// Increment H ROUND-TRIP: the contract below is the -suggest-contract
// output for mkStats (see Stats.bsv), pasted verbatim beside a
// package-local copy of the interface.  Suggestion is
// extract-then-freeze: pasting the output and recompiling checks
// clean by construction, so the member below (identical to mkStats)
// must conform to its own suggestion.

package StatsFrozen;

import List::*;

interface Stats;
   method Bit#(8) total();
   method Bool busy();
   method Action add(Bit#(8) x);
   method Action clear();
endinterface

// -- suggested contract for module `mkStats': ---------------------
List#(ContractStmt) contract_Stats =
   cons(contractCF("total", "clear"),
     cons(contractCF("total", "busy"),
     cons(contractSB("busy", "clear"),
     cons(contractSB("busy", "add"),
     cons(contractSB("total", "add"),
     cons(contractAlwaysReady("total"),
     cons(contractAlwaysReady("busy"),
     cons(contractAlwaysReady("clear"),
     nil))))))));
// -----------------------------------------------------------------

(* synthesize *)
module mkStatsFrozen(Stats);
   Reg#(Bit#(8))   t      <- mkReg(0);
   Reg#(Bool)      locked <- mkReg(False);
   RWire#(Bit#(8)) lastop <- mkRWire;

   method Bit#(8) total();
      return t;
   endmethod

   method Bool busy();
      return locked;
   endmethod

   method Action add(Bit#(8) x) if (!locked);
      t <= t + x;
      locked <= True;
      lastop.wset(x);
   endmethod

   method Action clear();
      locked <= False;
      lastop.wset(0);
   endmethod
endmodule

endpackage
