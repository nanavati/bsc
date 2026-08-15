function Bool incompleteReal(Real x);
   return (case (x) matches
              0.0: False;
              1.0: True;
           endcase);
endfunction

// Numeric equality identifies positive and negative zero.
function Bool redundantSignedZero(Real x);
   return (case (x) matches
              0.0: False;
              -0.0: True;
              default: True;
           endcase);
endfunction

// Prelude's Literal Real conversion is closed and canonicalizes 1 to 1.0.
function Bool redundantIntegerReal(Real x);
   return (case (x) matches
              1: False;
              1.0: True;
              default: True;
           endcase);
endfunction

function Bool completeReal(Real x);
   return (case (x) matches
              0.0: False;
              default: True;
           endcase);
endfunction

typedef struct {
   Bit#(1) value;
} TinyReal deriving (Bits, Eq);

instance RealLiteral#(TinyReal);
   function TinyReal fromReal(Real x);
      return TinyReal { value: 0 };
   endfunction
endinstance

// A custom conversion is arbitrary and therefore deliberately opaque.
function Bool opaqueCustomReal(TinyReal x);
   return (case (x) matches
              1.0: False;
              2.0: True;
           endcase);
endfunction
