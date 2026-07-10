// Two generated modules in ONE package, the second instantiating the
// first (the parent's user def references the sibling's generated
// module).  The captured skeleton of mkSibTop reaches mkSibSub only
// THROUGH the renamed user def -- a non-generated package def -- so
// the selective re-knot must refresh every same-package reference,
// not just the generated members: with the generated-members-only
// re-knot, elaboration of mkSibTop spun the evaluator forever on the
// stale pre-synthesis knot (found by bsc.scheduler's IgnoreRdy).

package SiblingInj;

interface Sub;
   method Action poke(Bit#(8) x);
   method Action bump();
endinterface

interface SibTop;
   method Action go(Bit#(8) x);
endinterface

(* synthesize *)
module mkSibSub(Sub);
   Reg#(Bit#(8)) r <- mkReg(0);
   method Action poke(Bit#(8) x);
      r <= x;
   endmethod
   method Action bump() if (r != 255);
      r <= r + 1;
   endmethod
endmodule

(* synthesize *)
module mkSibTop(SibTop);
   Sub s <- mkSibSub;
   rule do_bump;
      s.bump();
   endrule
   method Action go(Bit#(8) x);
      s.poke(x);
   endmethod
endmodule

endpackage
