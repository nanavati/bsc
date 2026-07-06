package PulseNoAR;

interface PulseNAR;
   method Action tick();
endinterface

List#(ContractStmt) contract_PulseNAR =
   cons(contractAlwaysEnabled("tick"), nil);

(* synthesize *)
module mkPulseNAR(PulseNAR);
   Reg#(Bit#(8)) cnt <- mkReg(0);
   method Action tick();
      cnt <= cnt + 1;
   endmethod
endmodule

(* synthesize *)
module sysCPulseNoAR(Empty);
   PulseNAR p <- mkOneOf(nil, mkPulseNAR);
   rule drive;
      p.tick();
   endrule
endmodule

endpackage
