(* synthesize *)
module sysIfCase();
   Reg#(Bit#(3)) rg <- mkReg(0);
   Reg#(Bit#(8)) rg2 <- mkRegU;
   rule r;
      Bit#(8) n;
      if (rg == 4)
         n = 22;
      else
         case (rg)
            0 : n = 17;
            1 : n = 42;
            2 : n = 2;
            default : n = 5;
         endcase
      rg2 <= n;
   endrule
endmodule
