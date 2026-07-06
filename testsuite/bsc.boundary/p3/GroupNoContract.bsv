// NEGATIVE: an implementation group requires its interface to declare
// a contract (no definition of contract_Plain exists).

import List::*;

interface Plain;
   method Bit#(8) get();
endinterface

(* synthesize *)
module mkPlainA(Plain);
   Reg#(Bit#(8)) r <- mkReg(0);
   method Bit#(8) get();
      return r;
   endmethod
endmodule

(* synthesize *)
module mkTbGroupNoContract();
   Plain p <- mkOneOf(cons(tuple2("alt", mkPlainA), nil), mkPlainA);
   rule show;
      $display("%0d", p.get());
      $finish(0);
   endrule
endmodule
