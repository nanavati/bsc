
// A two-input tri-state bus resolution node.
//
// Drive values arrive as (value, enable) PAIRS on ordinary ports, and
// every Z stays inside this module: the enables re-create the tri-state
// drivers on a module-local net, and the resolved value leaves through
// an ordinary (enable-masked) port.  This shape is load-bearing for
// portability: a structural two-state simulator (Verilator) analyzes
// tri-state statically, following Z-ness from 'bz literals through
// direct port-to-net connections only -- a Z VALUE carried through an
// output port onto an intermediate wire loses its Z-ness and degrades
// multi-driver resolution into a dropped driver.  Keeping the 'bz
// literals and the resolved net in one module is the one shape that
// event-driven four-state simulators, synthesis, and structural
// two-state simulators all agree on.
//
// OUT packs {CTL_OUT, VALUE}: driven-ness and the resolved value.  The
// value is CTL-masked, so an undriven bus reads as zeros everywhere
// (matching the library's reference semantics -- the pure Bluesim
// implementation masks by enable and resolves by OR).  The only
// simulator-class divergence left is the ILLEGAL multi-driver case
// (four-state resolves to X, a structural two-state simulator to the
// OR of the drivers); the ZBus library detects that case from the
// enables in plain logic and masks the value before any client reads
// it.
module ZResolveNode(IN_0, CTL_0, IN_1, CTL_1, OUT);

   parameter width = 1;

   input [width - 1 : 0]  IN_0;
   input                  CTL_0;
   input [width - 1 : 0]  IN_1;
   input                  CTL_1;
   output [width : 0]     OUT;

   tri [width - 1 : 0]    BUS;

   assign BUS = CTL_0 ? IN_0 : {width{1'bz}};
   assign BUS = CTL_1 ? IN_1 : {width{1'bz}};

   wire                   CTL_OUT;
   assign CTL_OUT = CTL_0 | CTL_1;

   assign OUT = {CTL_OUT, CTL_OUT ? BUS : {width{1'b0}}};

endmodule
