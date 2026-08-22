
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



module MakeReset0 (
		  CLK,
		  RST,
                  ASSERT_IN,
		  ASSERT_OUT,

                  OUT_RST
                  );

   parameter          init = 1 ;

   input              CLK ;
   input              RST ;
   input              ASSERT_IN ;
   output             ASSERT_OUT ;

   output             OUT_RST ;

   reg                rst ;

   assign ASSERT_OUT =  rst == `BSV_RESET_VALUE ;

   assign OUT_RST = rst ;

   always@(posedge CLK or `BSV_RESET_EDGE RST) begin
      if (RST == `BSV_RESET_VALUE)
        rst <= `BSV_ASSIGNMENT_DELAY init ? ~ `BSV_RESET_VALUE : `BSV_RESET_VALUE;
      else
        begin
           if (ASSERT_IN)
             rst <= `BSV_ASSIGNMENT_DELAY `BSV_RESET_VALUE;
           else // if (rst == 1'b0)
             rst <= `BSV_ASSIGNMENT_DELAY ~ `BSV_RESET_VALUE;
        end // else: !if(RST == `BSV_RESET_VALUE)
   end // always@ (posedge CLK or `BSV_RESET_EDGE RST)


`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   // Initialize to the value the reset branch would produce: the state
   // a simulator that saw the reset assertion edge at time 0 would
   // reach.  Initializing to the deasserted value contradicted the
   // reset branch: a two-state simulator (which sees no time-0 edge)
   // then held the generated reset deasserted until the harness's
   // manufactured assertion edge, and consumers of the INVERTED reset
   // observed that window as a spurious assertion of their own reset.
   initial begin
      rst = init ? ~ `BSV_RESET_VALUE : `BSV_RESET_VALUE ;
   end
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule // MakeReset0
