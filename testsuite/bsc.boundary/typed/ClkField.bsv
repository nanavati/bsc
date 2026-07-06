// Compile-only: Clock and Reset fields mediate by identity
// (MediateField Clock Clock / Reset Reset).  No simulation, since
// using the wrapped clock would need clocked_by plumbing; full
// elaboration through a backend is enough to exercise the instances.

interface ClkA;
   interface Clock cout;
   interface Reset rout;
   method Bit#(5) val();
endinterface

interface ClkB;
   interface Clock cout;
   interface Reset rout;
   method Bit#(5) val();
endinterface

(* synthesize *)
module mkClkImpl(ClkA);
   Clock c <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;
   Reg#(Bit#(5)) r <- mkReg(9);

   interface cout = c;
   interface rout = rst;

   method Bit#(5) val();
      return r;
   endmethod
endmodule

(* synthesize *)
module mkClkWrap();
   ClkA a <- mkClkImpl;

   ClkB b = genericWrapIfc(a);
   ClkA back = genericUnwrapIfc(b);

   rule show;
      $display("vals=%0d %0d", b.val(), back.val());
      $finish(0);
   endrule
endmodule
