function Bit#(3) classifyReal(Real x);
   return (case (x) matches
              -1.5: 0;
               0.0: 1;
               1.5: 2;
               default: 3;
           endcase);
endfunction

(* synthesize *)
module sysPatternReal();
   function m(s) = $display(message(s, s));

   rule r;
      if (classifyReal(-1.5) == 0)
         m("negative Real pattern");
      if (classifyReal(0.0) == 1)
         m("zero Real pattern");
      if (classifyReal(-0.0) == 1)
         m("negative zero uses numeric equality");
      if (classifyReal(1.5) == 2)
         m("positive Real pattern");
      if (classifyReal(2.5) == 3)
         m("Real pattern default");
   endrule
endmodule
