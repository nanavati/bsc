// Like RegNeverRead, but the module also has live logic, so the dead
// register is inlined into the parent rather than left as a submodule.
// Both the elaboration-time and the emission-time analyses can see it.
interface RegNeverReadInlined;
   method Bit#(8) result;
endinterface

(* synthesize *)
module mkRegNeverReadInlined (RegNeverReadInlined);
   Reg#(Bit#(8)) count <- mkReg(0);
   Reg#(Bit#(8)) sink  <- mkReg(0);

   rule go;
      count <= count + 1;
      sink  <= (count << 3) ^ 8'h5A;
   endrule

   method result = count;
endmodule
