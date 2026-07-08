// A hierarchical interface under injection: no skeleton is planted
// at GenWrap time -- the user's def stays top-level and intact, and
// the skeleton is constructed at genModule time.

interface SubIfc;
   method Action poke(Bit#(8) x);
   method Bit#(8) peek();
endinterface

interface HierIfc;
   method Bool ready();
   (* prefix = "SS" *)
   interface SubIfc sub;
endinterface

(* synthesize *)
module mkHierInj(HierIfc);
   Reg#(Bit#(8)) r <- mkReg(0);
   method ready = True;
   interface SubIfc sub;
      method Action poke(Bit#(8) x);
         r <= x;
      endmethod
      method peek = r._read;
   endinterface
endmodule
