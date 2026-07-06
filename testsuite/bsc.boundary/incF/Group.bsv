// Increment F (A97): an implementation group over a HIERARCHICAL
// interface.  The group-site inline-root protection must recognize
// the sub-interface as its flattened subtree (interface field `fifo'
// is present on the boundary as methods `fifo_*'), and sealing must
// accept the dotted atoms of contract_Outer.

package Group;

import List::*;
import Hier::*;

// An alternate implementation of the same contract: it stores x+1 on
// enq, so which member was selected is observable in the output.
(* synthesize *)
module mkOuterAlt(Outer);
   Reg#(Bit#(8)) data <- mkReg(0);
   Reg#(Bool)    full <- mkReg(False);

   interface Fifo1 fifo;
      method Action enq(Bit#(8) x) if (!full);
         data <= x + 1;
         full <= True;
      endmethod
      method Bit#(8) first();
         return data;
      endmethod
      method Action deq() if (full);
         full <= False;
      endmethod
   endinterface
endmodule

(* synthesize *)
module mkGroupHierTb(Empty);
   Outer o <- mkOneOf(cons(tuple2("alt", mkOuterAlt), nil), mkOuterImpl);
   Reg#(Bit#(8)) step <- mkReg(0);

   rule s0 (step == 0);
      o.fifo.enq(8'd42);
      step <= 1;
   endrule

   // first and deq in one rule: allowed because the SEALED schedule
   // carries the declared SB("fifo.first", "fifo.deq")
   rule s1 (step == 1);
      $display("first=%0d", o.fifo.first());
      o.fifo.deq();
      step <= 2;
   endrule

   rule s2 (step == 2);
      $finish(0);
   endrule
endmodule

endpackage
