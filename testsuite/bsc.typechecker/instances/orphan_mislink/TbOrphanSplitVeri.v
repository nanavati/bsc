// Verilog-boundary silent mislink for SplitPorts.
//
// mkLaneSource.v was generated in SplitFwd's import cone (port i = lane i);
// mkLaneSink.v was generated in SplitRev's cone (port i = lane 3-i).  The
// two orphan instances emit IDENTICAL port-name sets with identical widths,
// so the natural name-based hookup below -- the same connection any netlist
// integration tool would make -- links cleanly and crosses the lanes.
//
// The source puts 0x11 on lane 0; the sink's lane0 method reports 0x44.
// Nothing at any layer can catch this: each bsc compile was coherent, the
// port names and widths match exactly, and the simulator sees a perfectly
// well-formed netlist.  Within bsc, the two instances never share a symbol
// table, so even the duplicate-instance check is unreachable.

module TbOrphanSplitVeri();

  wire [7:0] l0, l1, l2, l3, first;

  // Both methods are purely combinational; clock and reset (if present)
  // are left unconnected.
  mkLaneSource source(.out_0(l0), .out_1(l1), .out_2(l2), .out_3(l3),
                      .RDY_out());

  // Name-based integration: lane i to lane i, by port name.
  mkLaneSink sink(.lane0_1_0(l0), .lane0_1_1(l1),
                  .lane0_1_2(l2), .lane0_1_3(l3),
                  .lane0(first), .RDY_lane0());

  initial begin
    #10;
    $display("lane 0 sent %h, lane0 method sees %h", l0, first);
    if (first !== l0)
      $display("SILENT SPLITPORTS MISLINK (lanes crossed)");
    else
      $display("LANES OK");
    $finish(0);
  end

endmodule
