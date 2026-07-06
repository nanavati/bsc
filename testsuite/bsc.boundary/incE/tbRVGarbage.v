// Hand-written master testbench that deliberately violates the
// classic enable protocol: EN_deq is tied high on every cycle, so
// requests ("garbage requests") are asserted during not-ready
// periods.  Under the retractable ready/valid convention the member
// must complete a transfer only on request AND ready, so `first'
// must hold on every cycle where RDY_deq was low, and advance by one
// on every cycle where RDY_deq was high.
module tbRVGarbage(CLK, RST_N);
  input CLK;
  input RST_N;

  wire       rdy;
  wire       rdy_first;
  wire [7:0] val;

  reg [7:0]  cycle;
  reg [7:0]  last_val;
  reg        last_rdy;
  reg        started;

  // the garbage request: enable high whether ready or not
  mkRVStream stream(.CLK(CLK),
                    .RST_N(RST_N),
                    .EN_deq(1'b1),
                    .RDY_deq(rdy),
                    .first(val),
                    .RDY_first(rdy_first));

  initial begin
    cycle   = 8'd0;
    started = 1'b0;
  end

  always @(posedge CLK) begin
    if (RST_N == 1'b1) begin
      $display("cycle %0d rdy %b first %0d", cycle, rdy, val);
      if (started) begin
        if (!last_rdy && val != last_val)
          $display("FAIL: state advanced on a not-ready request");
        if (last_rdy && val != (last_val + 8'd1))
          $display("FAIL: state held on a ready request");
      end
      last_val <= val;
      last_rdy <= rdy;
      started  <= 1'b1;
      cycle    <= cycle + 8'd1;
      if (cycle == 8'd11) begin
        $display("done");
        $finish(0);
      end
    end
  end
endmodule
