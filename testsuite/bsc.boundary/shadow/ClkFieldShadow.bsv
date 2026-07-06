// Shadow check, Clock/Reset output fields (modeled on
// typed/ClkField.bsv): interface Clock/Reset members are opaque
// entries in the boundary_ description; the checker matches them by
// name against the assembled output clock/reset.  Compile only.

package ClkFieldShadow;

interface ClkIfc;
   interface Clock cout;
   interface Reset rout;
   method Bit#(5) val();
endinterface

(* synthesize *)
module mkClkFieldShadow(ClkIfc);
   Clock c <- exposeCurrentClock;
   Reset r <- exposeCurrentReset;
   Reg#(Bit#(5)) x <- mkReg(9);

   interface cout = c;
   interface rout = r;

   method Bit#(5) val();
      return x;
   endmethod
endmodule

endpackage
