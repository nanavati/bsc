// Round trip through the typed layer: Alpha and Beta are distinct
// interface types with identical field names and shapes.  A wrapped
// Beta view of a synthesized Alpha instance, and the Alpha view
// recovered with genericUnwrapIfc, must both drive the same state.

interface Alpha;
   method Bit#(8) look();
   method Action poke(Bit#(8) x);
endinterface

interface Beta;
   method Bit#(8) look();
   method Action poke(Bit#(8) x);
endinterface

(* synthesize *)
module mkAlphaImpl(Alpha);
   Reg#(Bit#(8)) r <- mkReg(42);

   method Bit#(8) look();
      return r;
   endmethod

   method Action poke(Bit#(8) x);
      r <= x;
   endmethod
endmodule

(* synthesize *)
module mkWrapRT();
   Alpha a <- mkAlphaImpl;

   // wrap to the structurally identical Beta ...
   Beta b = genericWrapIfc(a);
   // ... and convert back
   Alpha a2 = genericUnwrapIfc(b);

   Reg#(Bit#(3)) step <- mkReg(0);

   rule s0 (step == 0);
      $display("wrap look=%0d", b.look());
      step <= 1;
   endrule

   rule s1 (step == 1);
      b.poke(8'd7);
      step <= 2;
   endrule

   rule s2 (step == 2);
      $display("unwrap look=%0d", a2.look());
      step <= 3;
   endrule

   rule s3 (step == 3);
      a2.poke(8'd99);
      step <= 4;
   endrule

   rule s4 (step == 4);
      $display("wrap again look=%0d", b.look());
      $finish(0);
   endrule
endmodule
