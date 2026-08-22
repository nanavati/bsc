// R2 negative: an output reset (refused in v1; Q1 default defers them).
interface Ifc;
   interface Reset rout;
   method Bit#(8) get();
endinterface

import "BVI" OutRst =
module mkOutRst(Ifc);
   default_clock clk(CLK);
   default_reset rst(RST_N);
   output_reset rout(RST_OUT);
   method OUT get();
   schedule get CF get;
endmodule

(* synthesize *)
module sysNegOutReset();
   let dut <- mkOutRst;
   rule r;
      $display("%0d", dut.get());
      $finish(0);
   endrule
endmodule
