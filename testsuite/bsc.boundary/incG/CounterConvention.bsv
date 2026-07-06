// Increment G negative (v0): a BVI cannot claim a convention-tagged
// interface.  convention_HsCounter declares the retractable
// ready/valid convention for "incr"; a hand-declared boundary cannot
// yet declare that realization, so the import is rejected at this
// package's compile.

package CounterConvention;

import List::*;

interface HsCounter;
   method Action incr();
endinterface

List#(ConventionStmt) convention_HsCounter =
   cons(conventionReadyValid("incr"), nil);

import "BVI" mkHsV = module mkHsCounter(HsCounter);
   default_clock clk(CLK);
   default_reset rst(RST_N);
   method incr() enable(EN_incr);
   schedule (incr) C (incr);
endmodule

endpackage
