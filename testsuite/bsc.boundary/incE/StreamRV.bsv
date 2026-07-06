package StreamRV;

interface Stream;
   method Action deq();
   method Bit#(8) first();
endinterface

List#(ConventionStmt) convention_Stream =
   cons(conventionReadyValid("deq"), nil);

(* synthesize *)
module mkRVStream(Stream);
   Reg#(Bit#(8)) data <- mkReg(0);
   Reg#(Bit#(2)) ph <- mkReg(0);

   rule spin;
      ph <= ph + 1;
   endrule

   method Action deq() if (ph == 0);
      data <= data + 1;
   endmethod

   method first = data;
endmodule

endpackage
