//Testcase

import Clocks::*;

interface SyncRegSlow_IFC;
 method Action start(Bit#(6) in_data1, Bit#(6) in_data2);
 method Bit#(7) out_data();
 interface Clock clk_slow;
 interface Reset rst_slow;
endinterface : SyncRegSlow_IFC

(*
   CLK = "clk_1",
   RST_N = "rst_1",
   synthesize
*)

module mkSyncRegSlow (Clock clk_fast, SyncRegSlow_IFC ifc);
 Clock currClk <- exposeCurrentClock;
 Reset currRst <- exposeCurrentReset;

 // The divider needs a reset in the clk_fast domain to give the divided
 // clock a defined phase; the module's own reset is synchronized over.
 // (An unreset divider self-corrects to the right period in hardware,
 // but its phase would rest on the counter's power-up value.)
 Reset                  rst_fast();
 mkAsyncResetFromCR#(2) t_rst_fast(clk_fast, rst_fast);

 ClockDividerIfc    div();
 mkClockDivider#(4) t_div(div, clocked_by clk_fast, reset_by rst_fast);

 // Async-assert form, per the library's own recommendation: the plain
 // synchronous form samples its input only at (divided-)clock edges,
 // and a time-0 edge race can leave it never asserting at all.
 Reset                  rst_n();
 mkAsyncResetFromCR#(3) t_rst_n(div.slowClock, rst_n);

 Reg#(Bit#(7))         out_data_reg() ;
 mkSyncRegToSlow#(0)   i_out_data_reg(div, rst_n, out_data_reg);

 method Action start(data1, data2);
	out_data_reg <= zeroExtend(data1) + zeroExtend(data2);
 endmethod : start

 method out_data();
   out_data=out_data_reg;
 endmethod : out_data

 interface Clock clk_slow = div.slowClock;

 interface Reset rst_slow = rst_n;
endmodule
