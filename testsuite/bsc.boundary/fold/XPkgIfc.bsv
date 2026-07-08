// The interface package: descriptions record each leaf's resolved
// method type at the declaration; a member module in ANOTHER package
// must verify those recorded types against its own inventory before
// the fold is allowed to fire.

package XPkgIfc;

interface XSub;
   method Action set(Bit#(8) v);
endinterface

interface XIfc;
   method Bit#(8) get();
   interface XSub sub;
endinterface

endpackage
