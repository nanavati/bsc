// Increment G negative: a BVI whose DECLARED schedule does not grant
// a declared CF.  contract_PairCtr declares CF("a", "b"); the import's
// schedule clauses only grant SB, so the boundary is rejected at this
// package's compile with the clause named.

package CounterBadSched;

import List::*;

interface PairCtr;
   method Bit#(8) a();
   method Bit#(8) b();
endinterface

List#(ContractStmt) contract_PairCtr =
   cons(contractCF("a", "b"), nil);

import "BVI" mkPairV = module mkPairBad(PairCtr);
   default_clock clk(CLK);
   default_reset rst(RST_N);
   method A_OUT a();
   method B_OUT b();
   schedule (a) CF (a);
   schedule (b) CF (b);
   schedule (a) SB (b);
endmodule

endpackage
