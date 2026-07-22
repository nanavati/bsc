// A sign extension to 64 bits whose only reader takes the low 8.  The top
// 56 bits are driven and never loaded.
(* synthesize *)
module mkNarrowExtDefs (Empty);
   Reg#(Bool) c <- mkReg(False);
   Reg#(Bit#(8)) out <- mkReg(0);

   rule go;
      Bit#(64) wide = signExtend(pack(c));
      out <= wide[7:0];
   endrule
endmodule
