// A literal pattern outside the type's domain is only diagnosed at
// elaboration; the checker must abandon the analysis rather than
// draw wrong conclusions from it.
function Bit#(2) f(Bit#(1) x);
   return (case (x) matches
              0: 2'd1;
              1: 2'd2;
              5: 2'd3;
           endcase);
endfunction

function Bit#(2) g(Bit#(1) x);
   return (case (x) matches
              0: 2'd0;
              5: 2'd1;
              .*: 2'd2;
           endcase);
endfunction

// widths too large to enumerate are treated as unbounded (and must
// not blow up compile time computing 2^n)
function Bit#(2) h(Bit#(100000000000) x);
   return (case (x) matches
              0: 2'd1;
              .*: 2'd2;
           endcase);
endfunction

// negative literals are not valid for UInt: the analysis is abandoned
// (elaborating such a match would report an invalid literal)
function Bit#(2) negUInt(UInt#(2) x);
   return (case (x) matches
              -1: 0;
              .*: 1;
           endcase);
endfunction
