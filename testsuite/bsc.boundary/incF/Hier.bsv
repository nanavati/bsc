// Increment F (A97): dotted method paths in contract atoms.
//
// `Outer' contains a sub-interface `fifo'; the contract beside it
// names the sub-interface's methods with dotted paths ("fifo.first"),
// following the grammar MethodPath ::= ident ("." ident)*.  The
// checker flattens each path to the boundary rendering that joins
// components with underscores ("fifo_first"), so a synthesized
// implementation of the hierarchical interface conforms.

package Hier;

import List::*;

interface Fifo1;
   method Action enq(Bit#(8) x);
   method Bit#(8) first();
   method Action deq();
endinterface

interface Outer;
   interface Fifo1 fifo;
endinterface

// The declared contract, using dotted-path atoms.
// (first reads the data slot, enq writes it: first SB enq holds; the
// actual first/deq relation is CF, which refines the declared SB.)
List#(ContractStmt) contract_Outer =
   cons(contractSB("fifo.first", "fifo.enq"),
   cons(contractSB("fifo.first", "fifo.deq"),
   cons(contractAlwaysReady("fifo.first"), nil)));

(* synthesize *)
module mkOuterImpl(Outer);
   Reg#(Bit#(8)) data <- mkReg(0);
   Reg#(Bool)    full <- mkReg(False);

   interface Fifo1 fifo;
      method Action enq(Bit#(8) x) if (!full);
         data <= x;
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
module mkHierTb(Empty);
   Outer o <- mkOuterImpl;
   Reg#(Bit#(8)) step <- mkReg(0);

   rule s0 (step == 0);
      o.fifo.enq(8'd42);
      step <= 1;
   endrule

   rule s1 (step == 1);
      $display("first=%0d", o.fifo.first());
      o.fifo.deq();
      step <= 2;
   endrule

   rule s2 (step == 2);
      o.fifo.enq(8'd7);
      step <= 3;
   endrule

   rule s3 (step == 3);
      $display("first=%0d", o.fifo.first());
      $finish(0);
   endrule
endmodule

endpackage
