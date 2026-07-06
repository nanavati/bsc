import Pulse::*;

(* synthesize *)
module sysCTopGood(Empty);
   Pulse p <- mkOneOf(cons(tuple2("b", mkPulseB), nil), mkPulseA);
   Reg#(Bit#(8)) n <- mkReg(0);

   rule drive;
      p.tick();
   endrule

   rule count;
      $display("tick %0d", n);
      if (n == 4) $finish(0);
      n <= n + 1;
   endrule
endmodule
