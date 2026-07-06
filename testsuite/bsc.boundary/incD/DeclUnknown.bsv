package DeclUnknown;

interface PokeU;
   method Action req(Bit#(8) x);
endinterface

List#(ConventionStmt) convention_PokeU =
   cons(conventionReadyValid("nosuch"), nil);

(* synthesize *)
module mkDeclUnknown(PokeU);
   Reg#(Bit#(8)) v <- mkReg(0);
   method Action req(Bit#(8) x);
      v <= x;
   endmethod
endmodule

endpackage
