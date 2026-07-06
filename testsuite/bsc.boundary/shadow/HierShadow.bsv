// Shadow check, hierarchical interface: the boundary_ description
// records dotted paths ("fifo.enq"); the assembled boundary renders
// them flattened ("fifo_enq").  The checker must agree with the
// flattening.  (Modeled on incF/Hier.bsv, minus the contract -- the
// concern here is only the hierarchy.)

package HierShadow;

interface Fifo1;
   method Action enq(Bit#(8) x);
   method Bit#(8) first();
   method Action deq();
endinterface

interface Outer;
   interface Fifo1 fifo;
endinterface

(* synthesize *)
module mkHierShadow(Outer);
   Reg#(Bit#(8)) data <- mkReg(0);
   Reg#(Bool)    full <- mkReg(False);

   interface Fifo1 fifo;
      method Action enq(Bit#(8) x) if (!full);
         data <= x;
         full <= True;
      endmethod
      method Bit#(8) first() if (full);
         return data;
      endmethod
      method Action deq() if (full);
         full <= False;
      endmethod
   endinterface
endmodule

endpackage
