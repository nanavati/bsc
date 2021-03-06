// This test is identical to OneModule.bsv, except that the rules and state
// for the two clock domains are in separately-synthesized modules which
// are clocked_by the two clocks.

// This is different from TwoSubmodulesClockedBy.bsv in that
// the clocks are coming as output clocks.

import Clocks::*;

// Clock periods
Integer p1 = 6;
Integer p2 = 4;

(* synthesize *)
module sysTwoSubmodulesClockedByOutputClock ();
   Clock clk1 <- mkAbsoluteClock(p1, p1);
   ClkSub clksub <- mkTwoSubmodulesClockedByOutputClock_ClkSub1;
   Clock clk2 = clksub.clk;

   mkTwoSubmodulesClockedByOutputClock_Sub1(clocked_by clk1, reset_by noReset);
   mkTwoSubmodulesClockedByOutputClock_Sub2(clocked_by clk2, reset_by noReset);
endmodule

// the initial value of the registers will be AA
Bit#(8) init_val = 8'hAA;

// function to make $stime the same for Bluesim and Verilog
function ActionValue#(Bit#(32)) adj_stime(Integer p);
   actionvalue
      let adj = (p + 1) / 2;
      let t <- $stime();
      if (genVerilog)
	 return (t + fromInteger(adj));
      else
	 return t;
   endactionvalue
endfunction

interface ClkSub;
   interface Clock clk;
endinterface

(* synthesize *)
module mkTwoSubmodulesClockedByOutputClock_ClkSub1 (ClkSub);
   Clock clk2 <- mkAbsoluteClock(p2, p2);
   interface Clock clk = clk2;
endmodule

(* synthesize *)
module mkTwoSubmodulesClockedByOutputClock_Sub1 ();
   // use RegU to avoid the need for a reset
   Reg#(Bit#(8)) rg1 <- mkRegU;

   rule r1;
      rg1 <= rg1 + 1;
      $display("(%d) rg1 = %h", adj_stime(p1), rg1);
   endrule

   rule stop (rg1 > (init_val + 17));
      $finish(0);
   endrule
endmodule

(* synthesize *)
module mkTwoSubmodulesClockedByOutputClock_Sub2 ();
   // use RegU to avoid the need for a reset
   Reg#(Bit#(8)) rg2 <- mkRegU;

   rule r2;
      rg2 <= rg2 + 1;
      $display("(%d) rg2 = %h", adj_stime(p2), rg2);
   endrule
endmodule

