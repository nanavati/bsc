// Negative: corresponding fields with different boundary shapes.
// Delta.poke takes Bit#(8) but Gamma.poke takes Bit#(16); the field
// pair has no common boundary method type, so genericWrapIfc must
// fail as an unresolved WrapMethod proviso naming the two field
// types.

interface Delta;
   method Bit#(8) look();
   method Action poke(Bit#(8) x);
endinterface

interface Gamma;
   method Bit#(8) look();
   method Action poke(Bit#(16) x);
endinterface

module mkShapeMismatch();
   Delta d = ?;
   Gamma g = genericWrapIfc(d);

   rule show;
      g.poke(16'd5);
   endrule
endmodule
