package DeclRV;

interface Pusher;
   method Action req(Bit#(8) x);
   method Bit#(8) last();
endinterface

List#(ConventionStmt) convention_Pusher =
   cons(conventionReadyValid("req"), nil);

(* synthesize *)
module mkPusher(Pusher);
   Reg#(Bit#(8)) v <- mkReg(0);
   Reg#(Bit#(1)) ph <- mkReg(0);

   rule flip;
      ph <= ph + 1;
   endrule

   method Action req(Bit#(8) x) if (ph == 0);
      v <= x;
   endmethod

   method last = v;
endmodule

endpackage
