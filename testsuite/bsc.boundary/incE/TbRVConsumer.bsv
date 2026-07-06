import StreamRV::*;

// A classic BSV consumer: the method call carries the implicit
// readiness condition, so the parent asserts EN only when RDY is
// high (EN implies ready) -- the retractable convention is invisible
// to a well-behaved caller.
(* synthesize *)
module sysERVConsumer(Empty);
   Stream s <- mkRVStream;
   Reg#(Bit#(8)) taken <- mkReg(0);

   rule take;
      s.deq();
      $display("got %0d", s.first);
      taken <= taken + 1;
      if (taken == 4) $finish(0);
   endrule
endmodule
