// NEGATIVE: a contract must be a literal list of contract statements
// with string-literal method names; any computation (here, map over a
// list and string concatenation) is rejected by the structural reader.

import List::*;

interface Gauge2;
   method Bit#(8) read();
endinterface

function ContractStmt mkStmt(String m);
   return contractAlwaysReady(strConcat("re", m));
endfunction

List#(ContractStmt) contract_Gauge2 =
   map(mkStmt, cons("ad", nil));

(* synthesize *)
module mkGauge2(Gauge2);
   Reg#(Bit#(8)) r <- mkReg(0);
   method Bit#(8) read();
      return r;
   endmethod
endmodule
