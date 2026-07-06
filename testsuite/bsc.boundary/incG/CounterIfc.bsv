// Increment G: the interface and its declared contract, shared by the
// generated and the hand-imported (BVI) implementations.  The contract
// is satisfiable by a ready-less boundary: a BVI method without a
// ready clause has constant readiness, and the generated members use
// always_ready.

package CounterIfc;

import List::*;

interface Counter;
   method Bit#(8) value();
   method Action incr();
endinterface

List#(ContractStmt) contract_Counter =
   cons(contractSB("value", "incr"),
   cons(contractAlwaysReady("value"),
   cons(contractAlwaysReady("incr"), nil)));

endpackage
