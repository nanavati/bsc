// Hand-written implementation of the Counter boundary (increment G).
// Counts up by 3 per enabled increment, so the selected group member
// is observable in simulation output.
//
// Ready-less boundary: no RDY_* outputs (readiness constant true),
// matching contractAlwaysReady in contract_Counter.
// Port shapes match the bsc-generated members: CLK, RST_N (negative
// reset), value output, EN_incr enable.

module mkCounterV(CLK, RST_N, value, EN_incr);
  input  CLK;
  input  RST_N;
  input  EN_incr;
  output [7:0] value;

  reg [7:0] count;

  assign value = count;

  always @(posedge CLK) begin
    if (RST_N == 1'b0)
      count <= 8'd0;
    else if (EN_incr)
      count <= count + 8'd3;
  end

endmodule
