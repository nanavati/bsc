package PulseValAE;

interface CntV;
   method Bit#(8) val();
endinterface

List#(ContractStmt) contract_CntV =
   cons(contractAlwaysReady("val"),
   cons(contractAlwaysEnabled("val"), nil));

(* synthesize *)
module mkCntV(CntV);
   Reg#(Bit#(8)) cnt <- mkReg(0);
   method val = cnt;
endmodule

(* synthesize *)
module sysCPulseValAE(Empty);
   CntV c <- mkOneOf(nil, mkCntV);
   rule show;
      $display("%0d", c.val);
   endrule
endmodule

endpackage
