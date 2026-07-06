package ScanDefs;

import List::*;

interface Pulse;
   method Action tick();
   method Bit#(8) cnt();
endinterface

List#(ContractStmt) contract_Pulse =
   cons(contractSB("cnt", "tick"),
   cons(contractAlwaysReady("cnt"), nil));

// The decoy: an unrelated interface whose name extends Pulse's, with
// a value-only shape (different kinds than Pulse's).
interface Pulse_AB;
   method Bit#(8) x();
endinterface

List#(ContractStmt) contract_Pulse_AB =
   cons(contractAlwaysReady("x"), nil);

// Members: the Pulse member carries always_ready, so its package
// emits only the AR-variant signature def (signature_Pulse_AR_...),
// never the plain signature_Pulse_.
(* synthesize, always_ready *)
module mkPulseAR(Pulse);
   Reg#(Bit#(8)) c <- mkReg(0);
   method Action tick();
      c <= c + 1;
   endmethod
   method Bit#(8) cnt();
      return c;
   endmethod
endmodule

(* synthesize, always_ready *)
module mkPulseARStub(Pulse);
   Reg#(Bit#(8)) c <- mkReg(0);
   method Action tick();
      c <= c + 1;
   endmethod
   method Bit#(8) cnt();
      return 0;
   endmethod
endmodule

(* synthesize *)
module mkPulseABImpl(Pulse_AB);
   method Bit#(8) x();
      return 5;
   endmethod
endmodule

endpackage
