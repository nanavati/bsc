// Verilog-boundary silent mislink for Bits.
//
// mkMsgSource.v was generated in a build where the orphan Bits instance
// (WireEnc) was visible; mkMsgSink.v was generated in a build where it was
// not.  Both modules expose the same logical type (Msg Hdr) as a 33-bit
// port, so any name/width-based netlist integration -- exactly what every
// SoC assembly flow does -- connects them cleanly.  The source drives
// src=aa, but the sink reads its src field through the derived layout and
// sees d5.  No tool at any layer has enough information to object.
//
// This connection SHOULD be ill-formed (the two artifacts disagree on the
// meaning of the 33 wires); today it links and simulates without a hitch.

module TbOrphanBitsVeri();

  wire [32:0] m;
  wire [7:0]  src;

  // Both methods are purely combinational; clock and reset (if present)
  // are left unconnected.
  mkMsgSource source(.out(m), .RDY_out());

  mkMsgSink sink(.srcOf_1(m), .srcOf(src), .RDY_srcOf());

  initial begin
    #10;
    $display("src field seen by sink: %h", src);
    if (src !== 8'haa)
      $display("SILENT BITS MISLINK (expected aa)");
    else
      $display("BITS OK");
    $finish(0);
  end

endmodule
