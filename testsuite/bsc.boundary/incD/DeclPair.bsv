package DeclPair;

interface Counter;
   method Action bump();
   method Bit#(8) value();
endinterface

List#(ContractStmt) contract_Counter =
   cons(contractSB("value", "bump"),
   cons(contractAlwaysReady("value"), nil));

List#(ConventionStmt) convention_Counter =
   cons(conventionReadyValid("bump"), nil);

(* synthesize *)
module mkCounterOnes(Counter);
   Reg#(Bit#(8)) n <- mkReg(0);
   Reg#(Bit#(1)) ph <- mkReg(0);

   rule flip;
      ph <= ph + 1;
   endrule

   method Action bump() if (ph == 0);
      n <= n + 1;
   endmethod

   method value = n;
endmodule

(* synthesize *)
module mkCounterTwos(Counter);
   Reg#(Bit#(8)) n <- mkReg(0);
   Reg#(Bit#(1)) ph <- mkReg(0);

   rule flip;
      ph <= ph + 1;
   endrule

   method Action bump() if (ph == 0);
      n <= n + 2;
   endmethod

   method value = n;
endmodule

endpackage
