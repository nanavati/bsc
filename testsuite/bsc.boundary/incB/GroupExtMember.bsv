// NEGATIVE (not currently constructible -- see incB.exp): a member
// whose boundary carries an external-conflict marker (nonempty sEXT)
// must be rejected from group formation ("carries an external-conflict
// marker; such a boundary cannot join a group yet" in ContractCheck's
// imposeDeclared).
//
// sEXT can only arise from a BVI import's `schedule EXT (m)'
// annotation, but the BSV parser's schedule auto-completion does not
// recognize EXT as covering the (m, m) self pair: it adds its own
// conflict annotation on top, and the doubly-annotated pair trips the
// VModInfo consistency check (an internal compiler error, independent
// of the group machinery).  This source is kept as the intended test
// input; enable the check in incB.exp once EXT annotations survive
// parsing.

import List::*;
import CounterSeal::*;

import "BVI" VExtCounter =
module mkCounterExt(Counter);
   default_clock clk(CLK);
   no_reset;
   method incr() enable(EN_incr);
   method VAL value();
   schedule value CF value;
   schedule value SB incr;
   schedule EXT incr;
endmodule

(* synthesize *)
module mkTbGroupExt();
   Counter c <- mkOneOf(cons(tuple2("tight", mkCounterTight), nil),
                        mkCounterExt);
   rule show;
      $display("%0d", c.value());
      $finish(0);
   endrule
endmodule
