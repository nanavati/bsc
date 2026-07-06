// Shadow check, simplest case: a flat interface with one method of
// each kind (value -> output/no enable, action -> enable/no output,
// actionvalue -> enable+output).  The boundary_ description and the
// assembled boundary must agree member-for-member; the Tb shows the
// flag does not perturb behavior.

package Flat;

interface Flat;
   method Bit#(8) getVal();
   method Action setVal(Bit#(8) x);
   method ActionValue#(Bit#(8)) bump();
endinterface

(* synthesize *)
module mkFlatDut(Flat);
   Reg#(Bit#(8)) state <- mkReg(0);

   method Bit#(8) getVal();
      return state;
   endmethod

   method Action setVal(Bit#(8) x);
      state <= x;
   endmethod

   method ActionValue#(Bit#(8)) bump();
      state <= state + 1;
      return state;
   endmethod
endmodule

(* synthesize *)
module mkFlatTb();
   Flat d <- mkFlatDut;
   Reg#(Bit#(2)) step <- mkReg(0);

   rule s0 (step == 0);
      d.setVal(10);
      step <= 1;
   endrule

   rule s1 (step == 1);
      let x <- d.bump();
      $display("bump %0d", x);
      step <= 2;
   endrule

   rule s2 (step == 2);
      $display("val %0d", d.getVal());
      $finish(0);
   endrule
endmodule

endpackage
