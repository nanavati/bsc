// Cross-package group, package 1 of 3: the interface and its declared
// contract live alone in this package.

import List::*;

interface CounterX;
   method Action incr();
   method Bit#(8) value();
endinterface

List#(ContractStmt) contract_CounterX =
   cons(contractSB("value", "incr"),
   cons(contractAlwaysReady("value"), nil));
