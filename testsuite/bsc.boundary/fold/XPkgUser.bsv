// The member package: synthesizes a module of an interface declared
// elsewhere; the fold reads the description (and its recorded types)
// across the package boundary.

package XPkgUser;

import XPkgIfc::*;

(* synthesize *)
module mkXPkgUser(XIfc);
   Reg#(Bit#(8)) r <- mkReg(0);
   method get = r._read;
   interface XSub sub;
      method Action set(Bit#(8) v);
         r <= v;
      endmethod
   endinterface
endmodule

endpackage
