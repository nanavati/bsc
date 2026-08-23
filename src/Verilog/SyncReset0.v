
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



module SyncReset0 (
		   IN_RST,
		   OUT_RST
		   );

   input   IN_RST ;
   output  OUT_RST ;

`ifdef VERILATOR
   // Two-state startup-edge emulation: regenerate the harness's
   // deassert/assert pulse (main.v, t=2..3) locally on the output.  A
   // pass-through wire forwards a pulse arriving on IN_RST, but when the
   // input is a generated reset (e.g. MakeReset0's register, a solid
   // asserted level from birth in two-state) no pulse ever arrives and
   // downstream async-assert consumers never see the asserting edge
   // that a four-state simulator delivers at time 0 (X -> asserted).
   // When IN_RST is deasserted at t=3 the mux returns to it and no
   // spurious assert edge is produced.  See SyncResetA.v for the full
   // rationale.
   reg     startup_pulse ;
   assign  OUT_RST = startup_pulse ? ~ `BSV_RESET_VALUE : IN_RST ;
   initial
     begin
        startup_pulse = 1'b0 ;
        #2 startup_pulse = 1'b1 ;
        #1 startup_pulse = 1'b0 ;
     end
`else
   assign  OUT_RST = IN_RST ;
`endif

endmodule
