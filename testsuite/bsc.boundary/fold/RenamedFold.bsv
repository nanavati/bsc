// prefix/result attributes on methods: the description's
// prefix/result slots are the fold's only source for these names --
// the renamed ports prove the naming flows from the description.

interface RenIfc;
   (* result = "nres" *)
   method Bit#(4) getv();
   (* prefix = "np" *)
   method Action setv(Bit#(4) v);
endinterface

(* synthesize *)
module mkRenamedFold(RenIfc);
   Reg#(Bit#(4)) r <- mkReg(0);
   method getv = r._read;
   method Action setv(Bit#(4) v);
      r <= v;
   endmethod
endmodule
