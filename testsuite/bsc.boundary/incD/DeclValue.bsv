package DeclValue;

interface PeekV;
   method Bit#(8) look();
endinterface

List#(ConventionStmt) convention_PeekV =
   cons(conventionReadyValid("look"), nil);

(* synthesize *)
module mkDeclValue(PeekV);
   Reg#(Bit#(8)) v <- mkReg(0);
   method look = v;
endmodule

endpackage
