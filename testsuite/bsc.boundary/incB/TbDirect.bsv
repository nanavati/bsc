// The counterfactual for TbSealing: instantiating mkCounterLoose
// directly (no group, no sealing) lets the parent schedule against
// the member's accidental value CF incr, so the scheduler keeps the
// rules in definition order (count_up before show).

import CounterSeal::*;

(* synthesize *)
module mkTbDirect();
   Counter c <- mkCounterLoose;
   Reg#(Bit#(8)) cycle <- mkReg(0);

   rule count_up;
      c.incr();
   endrule

   rule show;
      cycle <= cycle + 1;
      $display("value %0d", c.value());
      if (cycle == 6) $finish(0);
   endrule
endmodule
