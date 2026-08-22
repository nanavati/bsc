// R2 negative: an output clock (refused in v1; Q1 default defers them).
interface Ifc;
   interface Clock cout;
   method Bit#(8) get();
endinterface

import "BVI" OutClk =
module mkOutClk(Ifc);
   default_clock clk(CLK);
   default_reset rst(RST_N);
   output_clock cout(CLK_OUT);
   method OUT get();
   schedule get CF get;
endmodule

(* synthesize *)
module sysNegOutClock();
   let dut <- mkOutClk;
   rule r;
      $display("%0d", dut.get());
      $finish(0);
   endrule
endmodule
