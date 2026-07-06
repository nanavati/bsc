# incF: dotted method paths in contract atoms (increment F / A97)

Contract and convention atoms may name sub-interface methods with dotted
paths (`"fifo.enq"`, grammar `MethodPath ::= ident ("." ident)*`); the checker
flattens them to the underscore-joined boundary names. Positive tests cover a
hierarchical member and an implementation group over it (both simulated);
negatives check that malformed and vector-indexed paths get the grammar error.
