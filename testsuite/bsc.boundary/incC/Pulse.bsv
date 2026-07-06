package Pulse;

interface Pulse;
   method Action tick();
endinterface

List#(ContractStmt) contract_Pulse =
   cons(contractAlwaysReady("tick"),
   cons(contractAlwaysEnabled("tick"), nil));

(* synthesize *)
module mkPulseA(Pulse);
   Reg#(Bit#(8)) cnt <- mkReg(0);
   method Action tick();
      cnt <= cnt + 1;
   endmethod
endmodule

(* synthesize *)
module mkPulseB(Pulse);
   Reg#(Bit#(8)) cnt <- mkReg(0);
   method Action tick();
      cnt <= cnt + 2;
   endmethod
endmodule

endpackage
