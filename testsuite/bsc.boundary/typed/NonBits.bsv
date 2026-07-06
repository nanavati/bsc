// Negative: a non-Bits leaf (Integer value method) cannot cross a
// boundary, so genericWrapIfc must be rejected with a proviso naming
// the leaf (WrapMethod's value instance requires Bits).

interface RawA;
   method Integer bad();
   method Action poke(Bit#(8) x);
endinterface

interface RawB;
   method Integer bad();
   method Action poke(Bit#(8) x);
endinterface

module mkNonBits();
   RawA a = ?;
   RawB b = genericWrapIfc(a);

   rule show;
      b.poke(8'd0);
   endrule
endmodule
