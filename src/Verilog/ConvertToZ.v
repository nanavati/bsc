
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif


module ConvertToZ( IN, CTL, OUT);

   parameter width = 1;
   input [width - 1 : 0] 	IN;
   input 			CTL;
   output [width - 1 : 0]       OUT;
   
   tri [width - 1 : 0] 		BUS;
   
   
   `ifdef VERILATOR
   // Two-state simulators have no Z: once the tri passes through the
   // plain output port below, "undriven" becomes indistinguishable
   // from data and downstream ResolveZ joints resolve wrong (the bus
   // value dies at the first joint).  Encode "undriven" as all-zeros
   // instead; ResolveZ OR-resolves.  Faithful to the four-state
   // behavior whenever the bus protocol has at most one active driver
   // at a time -- the same discipline the Z encoding itself needs.
   assign BUS = CTL ? IN : {width{1'b0}};
`else
   assign BUS = CTL ? IN : 'bz;
`endif
   assign OUT = BUS;
   
endmodule






