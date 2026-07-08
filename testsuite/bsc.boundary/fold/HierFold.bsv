// A hierarchical interface: the fold must recurse through the
// subinterface (with a renaming prefix) exactly as the legacy walk
// does, consuming the description's dotted-path entries in DFS order.

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
module mkHierFold(HierIfc);
   Reg#(Bit#(8)) r <- mkReg(0);
   method ready = True;
   interface SubIfc sub;
      method Action poke(Bit#(8) x);
         r <= x;
      endmethod
      method peek = r._read;
   endinterface
endmodule
