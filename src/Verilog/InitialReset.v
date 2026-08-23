// This module is not synthesizable.

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



// A generator for resets from an absolute clock, starting at
// time 0. The output reset is held for RSTHOLD cycles, RSTHOLD > 0.

module InitialReset (
                     CLK,
                     OUT_RST
                     );

   parameter          RSTHOLD = 2  ; // Width of reset shift reg

   input              CLK ;
   output             OUT_RST ;

   // synopsys translate_off

   // The hold register is kept in a polarity-INDEPENDENT encoding
   // (0 = still asserting, 1 = done), inverted to the reset polarity
   // only at the output.  This makes the two-state pre-initial value
   // (zero) equal to the initialized value under BOTH polarities, so
   // the time-0 race between this initial block and a same-instant
   // shift (a derived clock can legitimately produce its one
   // assertion-time edge at time 0, clocking this register before or
   // after the init lands, in an order the LRM leaves open across
   // simulators) is benign by value.  In value encoding the race was
   // only masked under negative reset, where zero happens to BE the
   // asserted pattern; under positive reset a two-state simulator
   // could clobber the init with a shift computed from the deasserted
   // pre-initial state, and the held reset never happened.
   reg [RSTHOLD-1:0]  reset_hold ;
   wire [RSTHOLD:0] next_reset = {reset_hold, 1'b1} ;

   assign  OUT_RST = reset_hold[RSTHOLD-1] ? ~ `BSV_RESET_VALUE : `BSV_RESET_VALUE ;

   always @( posedge CLK )
     begin
        reset_hold <= `BSV_ASSIGNMENT_DELAY next_reset[RSTHOLD-1:0];
     end // always @ ( posedge CLK )

   initial
     begin
       // The #0 stays: this primitive has no reset input -- its own
       // X -> asserted output transition at time 0 IS the assertion
       // edge that derived async resets key on, and deferring it to
       // the inactive region guarantees every consumer process is
       // already waiting at its event control.
       #0
       reset_hold = { RSTHOLD { 1'b0 }} ;  // all bits to "asserting"
     end


   // synopsys translate_on

endmodule // InitialReset

