// Mixed-field round trip: a value method over a struct in Bits
// (Maybe#(Bit#(7))), a two-argument Action method, and an
// ActionValue#(Bit#(4)) method.  MixB's peek differs in
// representation (Bit#(8) vs Maybe#(Bit#(7))): the fields share the
// same 8-bit boundary type, so they mediate through WrapMethod's
// value instance (pack/unpack).

interface MixA;
   method Maybe#(Bit#(7)) peek();
   method Action set(Bit#(7) v, Bool valid);
   method ActionValue#(Bit#(4)) bump();
endinterface

interface MixB;
   method Bit#(8) peek();
   method Action set(Bit#(7) v, Bool valid);
   method ActionValue#(Bit#(4)) bump();
endinterface

(* synthesize *)
module mkMixImpl(MixA);
   Reg#(Maybe#(Bit#(7))) slot <- mkReg(tagged Valid 7'd21);
   Reg#(Bit#(4)) cnt <- mkReg(0);

   method Maybe#(Bit#(7)) peek();
      return slot;
   endmethod

   method Action set(Bit#(7) v, Bool valid);
      slot <= valid ? tagged Valid v : tagged Invalid;
   endmethod

   method ActionValue#(Bit#(4)) bump();
      cnt <= cnt + 1;
      return cnt;
   endmethod
endmodule

(* synthesize *)
module mkWrapMix();
   MixA a <- mkMixImpl;

   MixB b = genericWrapIfc(a);
   MixA back = genericUnwrapIfc(b);

   Reg#(Bit#(3)) step <- mkReg(0);

   rule s0 (step == 0);
      // pack (tagged Valid 7'd21) = 8'h95
      $display("wrap peek=%h", b.peek());
      step <= 1;
   endrule

   rule s1 (step == 1);
      b.set(7'd33, True);
      step <= 2;
   endrule

   rule s2 (step == 2);
      case (back.peek()) matches
         tagged Valid .v : $display("unwrap peek valid=%0d", v);
         tagged Invalid  : $display("unwrap peek invalid");
      endcase
      step <= 3;
   endrule

   rule s3 (step == 3);
      Bit#(4) x <- b.bump();
      $display("wrap bump=%0d", x);
      step <= 4;
   endrule

   rule s4 (step == 4);
      Bit#(4) y <- back.bump();
      $display("unwrap bump=%0d", y);
      step <= 5;
   endrule

   rule s5 (step == 5);
      Bit#(4) z <- b.bump();
      $display("wrap bump=%0d", z);
      $finish(0);
   endrule
endmodule
