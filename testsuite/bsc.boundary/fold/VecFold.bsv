// A vector of subinterfaces: the description carries one entry per
// concrete position, each with the index-erased `[_]' path (one
// shared WrapField codec per member); the fold expands them back to
// the concrete indexed leaves items_0_*, items_1_*, items_2_*.

import Vector::*;

interface Item;
   method Action put(Bit#(8) x);
   method Bit#(8) get();
endinterface

interface VecIfc;
   interface Vector#(3, Item) items;
endinterface

(* synthesize *)
module mkVecFold(VecIfc);
   Vector#(3, Reg#(Bit#(8))) rs <- replicateM(mkReg(0));

   Vector#(3, Item) is = newVector;
   for (Integer i = 0; i < 3; i = i + 1)
      is[i] = interface Item;
                 method Action put(Bit#(8) x);
                    rs[i] <= x;
                 endmethod
                 method get = rs[i]._read;
              endinterface;

   interface items = is;
endmodule
