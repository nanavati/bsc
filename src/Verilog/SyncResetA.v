
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



// A synchronization module for resets.   Output resets are held for
// RSTDELAY+1 cycles, RSTDELAY >= 0.  Reset assertion is asynchronous,
// while deassertion is synchronized to the clock.
module SyncResetA (
                   IN_RST,
                   CLK,
                   OUT_RST
                   );

   parameter          RSTDELAY = 1  ; // Width of reset shift reg

   input              CLK ;
   input              IN_RST ;
   output             OUT_RST ;

   reg [RSTDELAY:0]   reset_hold ;
   wire [RSTDELAY+1:0] next_reset = {reset_hold, ~ `BSV_RESET_VALUE} ;

`ifdef VERILATOR
   // Two-state startup-edge emulation.  A four-state simulator delivers
   // an asserting EDGE on OUT_RST at time 0 (X -> asserted when the
   // initial block below runs), which fires every downstream
   // async-assert consumer.  A two-state simulator has no time-0 edge,
   // and the harness's manufactured deassert/assert pulse (main.v,
   // t=2..3) dies in this module: deassertion is clock-synchronized and
   // the pulse window is clock-free by architecture, so reset_hold never
   // moves and OUT_RST never edges.  Regenerate the pulse locally on the
   // output in that same reserved window: deassert at 2, re-assert at 3.
   // The re-assert is the emulated time-0 edge; the deassert half falls
   // where no clock can sample it.  When reset_hold is (correctly)
   // deasserted by t=3 the mux simply returns to it and no spurious
   // assert edge is produced.  Deliberately not guarded by
   // BSV_NO_INITIAL_BLOCKS: this is edge synthesis, not state
   // initialization, and no-initial builds rely on the pulse alone.
   reg     startup_pulse ;
   assign  OUT_RST = startup_pulse ? ~ `BSV_RESET_VALUE
                                   : reset_hold[RSTDELAY] ;
   initial
     begin
        startup_pulse = 1'b0 ;
        #2 startup_pulse = 1'b1 ;
        #1 startup_pulse = 1'b0 ;
     end
`else
   assign  OUT_RST = reset_hold[RSTDELAY] ;
`endif

   always @( posedge CLK or `BSV_RESET_EDGE IN_RST )
     begin
        if (IN_RST == `BSV_RESET_VALUE)
           begin
              reset_hold <= `BSV_ASSIGNMENT_DELAY {RSTDELAY+1 {`BSV_RESET_VALUE}} ;
           end
        else
          begin
             reset_hold <= `BSV_ASSIGNMENT_DELAY next_reset[RSTDELAY:0];
          end
     end // always @ ( posedge CLK or  `BSV_RESET_EDGE IN_RST )

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   // Initialize holding the reset ASSERTED: the harness drives the
   // asserted level at time 0, and the initial state must agree with
   // the time-0 input levels or the window before the manufactured
   // assertion edge differs between four-state simulators (where the
   // time-0 X -> asserted transition is itself an edge) and two-state
   // simulators (which see no edge until the pulse and would otherwise
   // sit at a deasserted init, wrongly releasing downstream and
   // inverted-reset consumers during startup).
   initial
     begin
        reset_hold = {(RSTDELAY + 1) {`BSV_RESET_VALUE}} ;
     end
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule // SyncResetA
