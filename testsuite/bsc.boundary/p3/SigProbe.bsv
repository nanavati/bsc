// Introspect the compiler-emitted signature def of the Counter
// interface (signature_<flatifc>, here signature_Counter_) and
// messageM a formatted rendering of its (path, slots) entries.
// The def lands in the defining package's .bo like any other def, so
// an importing package can read it as ordinary data.

import List::*;
import CounterDefs::*;

(* synthesize *)
module mkSigProbe();
   function String fmtSlot(Tuple2#(String, String) slot);
      return strConcat(strConcat(strConcat(" ", tpl_1(slot)), "="),
                       tpl_2(slot));
   endfunction

   function String fmtEntry(Tuple2#(String, List#(Tuple2#(String, String))) ent);
      return strConcat(strConcat("\n  ", tpl_1(ent)),
                       foldl(strConcat, "", map(fmtSlot, tpl_2(ent))));
   endfunction

   messageM(strConcat("Counter signature:",
                      foldl(strConcat, "", map(fmtEntry, signature_Counter_))));
endmodule
