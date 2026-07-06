// Sealing soundness (A100): the group seals the root's boundary at
// the declared contract, so the parent schedules against the declared
// value SB incr even though mkCounterLoose's own schedule has the
// extra freedom value CF incr.  The rule using value (show) must
// therefore execute before the rule using incr (count_up), flipping
// the definition order that TbDirect exhibits.
//
// Register reads return start-of-cycle values regardless of rule
// order, so the $display output is deterministic; it differs only by
// which member is selected (loose: value stuck at 0; tight: counts).

import List::*;
import CounterSeal::*;

(* synthesize *)
module mkTbSealing();
   Counter c <- mkOneOf(cons(tuple2("tight", mkCounterTight), nil),
                        mkCounterLoose);
   Reg#(Bit#(8)) cycle <- mkReg(0);

   // defined first, so that without the sealed value SB incr the
   // scheduler would keep definition order (count_up before show)
   rule count_up;
      c.incr();
   endrule

   rule show;
      cycle <= cycle + 1;
      $display("value %0d", c.value());
      if (cycle == 6) $finish(0);
   endrule
endmodule
