// negative literal patterns: as in expressions, "-lit" matches the
// value (negate lit), which wraps around for unsigned types

// all four values of Int#(2): exhaustive
function Bit#(2) allInt(Int#(2) x);
   return (case (x) matches
              -2: 0;
              -1: 1;
              0: 2;
              1: 3;
           endcase);
endfunction

// missing -2
function Bit#(2) missingNeg(Int#(2) x);
   return (case (x) matches
              -1: 1;
              0: 2;
              1: 3;
           endcase);
endfunction

// -1 can never match after all values are covered positionally
function Bit#(2) dupNeg(Int#(2) x);
   return (case (x) matches
              -2: 0;
              -1: 1;
              0: 2;
              1: 3;
              -1: 1;
           endcase);
endfunction

// on Bit#(2), -1 wraps to 3: together with 0..2 this is exhaustive
function Bit#(2) wrapNeg(Bit#(2) x);
   return (case (x) matches
              0: 0;
              1: 1;
              2: 2;
              -1: 3;
           endcase);
endfunction

// ... and 3 after -1 can never match
function Bit#(2) wrapDup(Bit#(2) x);
   return (case (x) matches
              -1: 3;
              3: 0;
              default: 1;
           endcase);
endfunction
