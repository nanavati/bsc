
`ifdef BSV_NO_MAIN_V
`else

`ifdef BSV_ASSIGNMENT_DELAY
`else
  `define BSV_ASSIGNMENT_DELAY
`endif

`ifdef BSV_POSITIVE_RESET
  `define BSV_RESET_VALUE 1'b1
  `define BSV_RESET_EDGE posedge
`else
  `define BSV_RESET_VALUE 1'b0
  `define BSV_RESET_EDGE negedge
`endif

`ifdef BSV_RESET_NAME
`else
 `define BSV_RESET_NAME RST_N
`endif

`ifdef BSV_TIMESCALE
 `timescale `BSV_TIMESCALE
`endif

module main();

   reg CLK;
   // reg CLK_GATE;
   reg RST;
   reg [31:0] cycle;
   reg        do_vcd;
   reg        do_fsdb;
   reg        do_fst;
   reg        do_cycles;

   `TOP top(.CLK(CLK), /* .CLK_GATE(CLK_GATE), */ .`BSV_RESET_NAME(RST));

// For Sce-Mi linkage, insert code here
`ifdef BSV_SCEMI_LINK
`include `BSV_SCEMI_LINK
`endif

`ifdef BSV_DUMP_LEVEL
`else
 `define BSV_DUMP_LEVEL 0
`endif

`ifdef BSV_DUMP_TOP
`else
 `define BSV_DUMP_TOP main
`endif

   reg [8*256:1] filename;        // VCD dump file
   reg [8*256:1] fst_filename;    // FST dump file
   reg [8*256:1] fsdb_filename;   // FSDB dump file

   initial begin
      // CLK_GATE = 1'b1;
      // CLK = 1'b0;    // This line will cause a neg edge of clk at t=0!
      // RST = !`BSV_RESET_VALUE'b0;  // This needs #0, to allow always blocks to wait
      cycle = 0;

      do_vcd    = $test$plusargs("bscvcd") ;
      do_fst    = $test$plusargs("bscfst") ;
      do_fsdb   = $test$plusargs("bscfsdb") ;
      do_cycles = $test$plusargs("bsccycle") ;

      if ($value$plusargs("bscvcd=%s", filename))
	do_vcd = 1; // avoids bug in cvc
      else if (do_vcd)
	filename = "dump.vcd";

      if ($value$plusargs("bscfst=%s", fst_filename))
	do_fst = 1;
      else if (do_fst)
	fst_filename = "dump.fst";

      if ($value$plusargs("bscfsdb=%s", fsdb_filename))
	do_fsdb = 1; // avoids bug in cvc
      else if (do_fsdb)
	fsdb_filename = "dump.fsdb";

      // FSDB uses its own system tasks, available only when the Verdi PLI was
      // linked (BSC_FSDB defined); it can coexist with a VCD/FST dump below.
`ifdef BSC_FSDB
      if (do_fsdb) begin
         $fsdbDumpfile(fsdb_filename);
         $fsdbDumpvars(`BSV_DUMP_LEVEL, `BSV_DUMP_TOP);
      end
`else
      if (do_fsdb)
	$display("ERROR: %m was not built with FSDB support (rebuild with -dump-formats fsdb)");
`endif

      // VCD and FST share $dumpfile/$dumpvars; the on-disk format for FST is
      // selected by the simulator at run time (e.g. iverilog: vvp -fst), so a
      // build runs at most one of them -- FST takes precedence if both are asked.
      // With -dump-formats none the build script defines BSC_NO_DUMP: the dump
      // trigger is compiled out and a request errors loudly instead of dumping.
`ifdef BSC_NO_DUMP
      if (do_fst || do_vcd)
	$display("ERROR: %m was built with -dump-formats none; no waveform dumping is available");
`else
      if (do_fst) begin
         $dumpfile(fst_filename);
         $dumpvars(`BSV_DUMP_LEVEL, `BSV_DUMP_TOP);
      end
      else if (do_vcd) begin
         $dumpfile(filename);
         $dumpvars(`BSV_DUMP_LEVEL, `BSV_DUMP_TOP);
      end
`endif

      // Reset sequence: asserted as a level from time 0, then one
      // deassert/assert pulse so the assertion is also a genuine EDGE,
      // then one clock edge under reset, then release between clock
      // edges.  Asserting asynchronously -- away from any clock edge --
      // is required because clock-generating logic (dividers, gates)
      // can only be reset asynchronously: no clean derived clock exists
      // until it has been reset.  CLK is deliberately left
      // uninitialized until the first posedge (an X -> 1 transition is
      // not a negedge), as before.
      //
      // Nothing in the design's observable behavior should depend on
      // the window before its reset deasserts; the first clock edge of
      // the steady schedule is unchanged (negedge 5, posedge 10).
      //
      // BSV_LEGACY_RESET restores the previous choreography (assert in
      // the time-0 inactive region, first posedge at 1, deassert at 2),
      // as a one-release migration aid for environments with golden
      // files that recorded output from the startup window.
`ifdef BSV_LEGACY_RESET
      #0
      RST = `BSV_RESET_VALUE;
      #1;
      CLK = 1'b1;
      #1;
      RST = !`BSV_RESET_VALUE;
`else
      // t=0: asserted as a LEVEL.  Initial blocks (including the
      // primitives' own) run in the first time-0 inactive batch; any
      // clocked process an init-caused transition triggers reads its
      // guards at a strictly later batch, so this write is ordered
      // before every such read -- time-0 initialization artifacts in
      // four-state simulators are suppressed deterministically, not by
      // scheduler luck.
      #0
      RST = `BSV_RESET_VALUE;
      // t=1..2: one deassert/assert pulse, making the assertion a
      // genuine value EDGE.  Two-state simulators (no X, no time-0
      // edge) and BSV_NO_INITIAL_BLOCKS builds (no initialized state)
      // rely on this edge alone; four-state simulators see the same
      // edge, so the async-assert primitives fire identically
      // everywhere.  No clock edge coincides with either transition.
      #1;
      RST = !`BSV_RESET_VALUE;
      #1;
      RST = `BSV_RESET_VALUE;
      // t=3: first clock edge, under reset
      #1;
      CLK = 1'b1;
      // t=4: release, between clock edges; deassertion is synchronized
      // per-domain by the reset primitives
      #1;
      RST = !`BSV_RESET_VALUE;
`endif
      //  #200010;
      //  $finish;
   end

`ifndef NO_CLOCK // for cosim
   always
     begin
        #1
        if (do_cycles)
          $display("cycle %0d", cycle) ;
        cycle = cycle + 1 ;
        #4;
        CLK = 1'b0 ;
        #5;
        CLK = 1'b1 ;
     end // always begin
`endif //  `ifndef NO_CLOCK


endmodule

`endif
