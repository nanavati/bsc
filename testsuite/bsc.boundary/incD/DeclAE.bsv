package DeclAE;

interface PokeA;
   method Action req(Bit#(8) x);
endinterface

List#(ConventionStmt) convention_PokeA =
   cons(conventionReadyValid("req"), nil);

(* synthesize, always_enabled = "req" *)
module mkDeclAE(PokeA);
   Reg#(Bit#(8)) v <- mkReg(0);
   method Action req(Bit#(8) x);
      v <= x;
   endmethod
endmodule

endpackage
