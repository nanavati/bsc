
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


// A clock divider circuit.
// Division is based on the parameters, where
// Division is upper - lower + 1
// Duty cycle is :
//       let half = 1 << (width-1)
//       (upper - half) / upper - lower + 1
// E.g., (2,1,3) is a divide by 3  duty cycle  2/3
//       (2,0,3) is a divide by 4  duty cycle  2/4
//       (1,0,1) is a divide by 2, duty cycle  1/2
//       (3,1,5) is a divide by 5  duty cycle  2/5
//       (3,2,6) is a divide by 5  duty cycle  3/5
// The offset allow edges for separate modules to be determined
// relative to each other. a clock divider with offset 1 occurs one
// (fast) clock later than a clock with offset 0.
module ClockDiv(CLK_IN, RST, PREEDGE,  CLK_OUT);

   parameter width = 2 ;        // must be sufficient to hold upper
   parameter lower = 1 ;        //
   parameter upper = 3 ;
   parameter offset = 0;        // offset for relative edges.
                                // (0 <= offset <= (upper - lower)

   input     CLK_IN;            // input clock
   input     RST;

   output    PREEDGE;           // output signal announcing an upcoming edge
   output    CLK_OUT;           // output clock

   reg [ width -1 : 0 ] cntr ;
   reg                  PREEDGE ;

   // Wire constants for the parameters
   wire [width-1:0]     upper_w ;
   wire [width-1:0]     lower_w ;

`ifdef VERILATOR
   // Two-state emulation of the four-state virgin-counter behavior,
   // needed when RST is tied off (reset_by noReset): with no reset
   // edge to define it, a four-state counter is X until the first
   // CLK_IN edge, where (X < upper) is false and the else arm loads
   // 'lower' -- a defined phase.  Two-state C++-zero would instead
   // INCREMENT from zero, putting the divided clock one fast period
   // early.  Start the counter at all-ones (>= upper at any width, so
   // the first edge loads 'lower' identically), and gate CLK_OUT low
   // until the first always firing so the init itself makes no time-0
   // output transition (rule 1); a reset assertion opens the gate at
   // the assertion edge, matching the four-state X -> value edge.
   reg                  cd_started ;
   assign               CLK_OUT = cd_started ? cntr[width-1] : 1'b0 ;
   initial
     begin
        cd_started = 1'b0 ;
        cntr = {width{1'b1}} ;
     end
`else
   assign               CLK_OUT = cntr[width-1] ;
`endif
   assign               upper_w = upper ;
   assign               lower_w = lower ;

   // The clock is about to tick when counter is about to set its msb
   //  Note some simulators do not allow 0 width expressions
   wire [width-1:0]     nexttick = ~ ( 'b01 << (width-1) )  ;

   // Combinational block to generate next edge signal
   always@( cntr or nexttick )
     begin
        // The nonblocking assignment use to delay the update of the edge ready signal
        // Since this read by other always blocks trigger by the output CLK of this module
        #0
        PREEDGE <= `BSV_ASSIGNMENT_DELAY  (cntr == nexttick) ;
     end

   always@( posedge CLK_IN or `BSV_RESET_EDGE RST )
     begin
        // The use of blocking assignment within this block insures
        // that the clock generated from cntr[MSB] occurs before any
        // LHS of nonblocking assignments also from CLK_IN occur.
        // Basically, this insures that CLK_OUT and CLK_IN occur within
        // the same phase of the execution cycle,  before any state
        // updates occur. see
        // http://www.sunburst-design.com/papers/CummingsSNUG2002Boston_NBAwithDelays.pdf

`ifdef VERILATOR
        cd_started = 1'b1 ;
`endif
        if ( RST == `BSV_RESET_VALUE )
          cntr = upper - offset ;
        else
          begin
             if ( cntr < upper_w )
               cntr = cntr + 1 ;
             else
               cntr = lower_w ;
          end // else: !if( RST == `BSV_RESET_VALUE )
     end // always@ ( posedge CLK_IN or `BSV_RESET_EDGE RST )

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
  // synopsys translate_off
  // The counter is deliberately NOT initialized at time 0: CLK_OUT is a
  // bit of it, and a time-0 X -> value assignment is an edge in
  // four-state simulators (firing clocked processes before reset) but
  // not in two-state ones.  The counter is defined by the reset
  // assertion edge instead (matching BSV_NO_INITIAL_BLOCKS builds).
  initial
    begin
       PREEDGE = 0 ;
    end // initial begin
  // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS


endmodule // ClockDiv
