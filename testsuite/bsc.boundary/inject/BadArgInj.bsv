// A module argument with no Bits instance: still an error under
// injection (the skeleton's provisos are solved by the per-module
// pipeline at genModule time -- the phase moves, the message does
// not disappear).

typedef struct {
   Integer n;
} NotBits;

interface BIfc;
   method Bool valid();
endinterface

(* synthesize *)
module mkBadArgInj#(NotBits nb)(BIfc);
   method valid = True;
endmodule
