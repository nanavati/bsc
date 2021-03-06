// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.

  bit fire_2state, fire_xcheck, fire_cover;

`ifdef OVL_ASSERT_ON

`ifdef OVL_XCHECK_OFF
`else

  always @(posedge clk)
    fire_xcheck = 0;

  property ASSERT_NEVER_UNKNOWN_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  qualifier |-> !($isunknown(test_expr));
  endproperty

`endif // OVL_XCHECK_OFF

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
        A_ASSERT_NEVER_UNKNOWN_P:
        assert property (ASSERT_NEVER_UNKNOWN_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
          fire_xcheck = ovl_fire_xcheck_f(property_type);
        end 
`endif // OVL_XCHECK_OFF

      end
      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
        M_ASSERT_NEVER_UNKNOWN_P: assume property (ASSERT_NEVER_UNKNOWN_P);
`endif // OVL_XCHECK_OFF

      end
      `OVL_IGNORE : begin : ovl_ignore
        // do nothing;
      end
      default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");
    endcase

  endgenerate

`endif // OVL_ASSERT_ON

`ifdef OVL_COVER_ON

generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover
     if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

      cover_qualifier:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     qualifier) ) begin
                       ovl_cover_t("qualifier covered");
                       fire_cover = ovl_fire_cover_f(coverage_level);
                     end
     end //basic coverage

     if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

      cover_test_expr_change:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) && ($past(`OVL_RESET_SIGNAL) != 1'b0) &&
                     qualifier && !$stable(test_expr) ) ) begin
                       ovl_cover_t("test_expr_change covered");
                       fire_cover = ovl_fire_cover_f(coverage_level);
                     end
     end //sanity coverage
    end

endgenerate

`endif // OVL_COVER_ON
