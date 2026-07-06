// NEGATIVE: RDY_* names never appear in contracts; readiness is the
// method's own offer aspect (contractAlwaysReady), not a sibling
// method.

import List::*;

interface Gauge;
   method Bit#(8) read();
endinterface

List#(ContractStmt) contract_Gauge =
   cons(contractCF("RDY_read", "read"), nil);

(* synthesize *)
module mkGauge(Gauge);
   Reg#(Bit#(8)) r <- mkReg(0);
   method Bit#(8) read();
      return r;
   endmethod
endmodule
