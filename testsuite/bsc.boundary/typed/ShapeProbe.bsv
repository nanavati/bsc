// Compile-time introspection: synthShape reports the boundary
// decomposition of an interface as a List#(String).  Fold it into a
// single string and messageM it; the .exp checks the compile output.

import List::*;

interface ProbeIfc;
   method Bit#(8) look();
   method Action poke(Bit#(8) x);
   method ActionValue#(Bit#(4)) grab();
endinterface

// join a List#(String) with " | " (no such helper in the List
// library for plain Strings, so fold by hand)
function String joinShape(List#(String) xs);
   if (isNull(xs))
      return "";
   else if (isNull(tail(xs)))
      return head(xs);
   else
      return strConcat(head(xs), strConcat(" | ", joinShape(tail(xs))));
endfunction

(* synthesize *)
module sysShapeProbe();
   ProbeIfc proxy = ?;
   messageM(strConcat("shape: ", joinShape(synthShape(proxy))));
endmodule
