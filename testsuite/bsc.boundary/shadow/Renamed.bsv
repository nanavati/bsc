// Shadow check, renamed ports: prefix/result attributes change the
// port names that the boundary_ description's prefix/result slots
// carry; the checker must compare the renamed names, not the
// defaults.  (Attribute syntax as in bsc.names/portRenaming.)

package Renamed;

interface RenIfc;
   (* prefix = "ld" *)
   method Action load(Bit#(8) a);
   (* result = "sumval" *)
   method Bit#(8) sum(Bit#(8) b);
   (* prefix = "gr", result = "grabval" *)
   method ActionValue#(Bit#(8)) grab(Bit#(8) c);
endinterface

(* synthesize *)
module mkRenamed(RenIfc);
   Reg#(Bit#(8)) acc <- mkReg(0);

   method Action load(Bit#(8) a);
      acc <= a;
   endmethod

   method Bit#(8) sum(Bit#(8) b);
      return acc + b;
   endmethod

   method ActionValue#(Bit#(8)) grab(Bit#(8) c);
      acc <= acc + c;
      return acc;
   endmethod
endmodule

endpackage
