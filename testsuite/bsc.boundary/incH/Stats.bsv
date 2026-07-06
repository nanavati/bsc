// Increment H: a module with a distinctive inferred schedule, used to
// exercise -suggest-contract (the A25 migration aid).
//
// Inferred relations (t = total's register, locked = busy's register,
// lastop = an RWire both actions write):
//   total CF busy    (reads of different registers)  -> contractCF
//   total CF clear   (clear does not touch t)        -> contractCF
//   total SB add     (add writes t)                  -> contractSB
//   busy  SB add     (add writes locked)             -> contractSB
//   busy  SB clear   (clear writes locked)           -> contractSB
//   add   C  clear   (both wset the same RWire, a single-use
//                     resource; not declarable, omitted)
// Constant readiness: total, busy, and clear are unguarded ->
//   contractAlwaysReady for exactly those three; add is guarded.

package Stats;

interface Stats;
   method Bit#(8) total();
   method Bool busy();
   method Action add(Bit#(8) x);
   method Action clear();
endinterface

(* synthesize *)
module mkStats(Stats);
   Reg#(Bit#(8))   t      <- mkReg(0);
   Reg#(Bool)      locked <- mkReg(False);
   RWire#(Bit#(8)) lastop <- mkRWire;

   method Bit#(8) total();
      return t;
   endmethod

   method Bool busy();
      return locked;
   endmethod

   method Action add(Bit#(8) x) if (!locked);
      t <= t + x;
      locked <= True;
      lastop.wset(x);
   endmethod

   method Action clear();
      locked <= False;
      lastop.wset(0);
   endmethod
endmodule

endpackage
