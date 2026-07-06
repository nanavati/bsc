import DeclPair::*;

(* synthesize *)
module sysDDeclPair(Empty);
   Counter c <- mkOneOf(cons(tuple2("twos", mkCounterTwos), nil),
                        mkCounterOnes);
   Reg#(Bit#(8)) cyc <- mkReg(0);

   rule step;
      c.bump();
      $display("bump at value %0d", c.value);
   endrule

   rule clock;
      cyc <= cyc + 1;
      if (cyc == 9) begin
         $display("final value %0d", c.value);
         $finish(0);
      end
   endrule
endmodule
