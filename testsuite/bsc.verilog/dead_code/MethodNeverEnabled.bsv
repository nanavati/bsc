// A submodule action method that nothing ever enables.  The dual of an
// unused value method result: nothing consumes what "val" produces is
// G0137, nothing ever calls "reset_it" is G0138.
//
// The two action methods write different state on purpose -- two methods
// writing one register shadow each other, which is a different warning and
// not what this is testing.
interface Sink;
   method Action push(Bit#(8) x);
   method Action reset_it;
   method Bit#(8) val;
   method Bool wasReset;
endinterface

(* synthesize *)
module mkSink (Sink);
   Reg#(Bit#(8)) r <- mkReg(0);
   Reg#(Bool) flag <- mkReg(False);
   method Action push(Bit#(8) x); r <= x; endmethod
   method Action reset_it; flag <= True; endmethod
   method val = r;
   method wasReset = flag;
endmodule

(* synthesize *)
module mkMethodNeverEnabled (Empty);
   Sink s <- mkSink;
   Reg#(Bit#(8)) c <- mkReg(0);

   rule go;
      c <= c + 1;
      s.push(c);
   endrule

   rule show;
      $display("%d", s.val);
   endrule
endmodule
