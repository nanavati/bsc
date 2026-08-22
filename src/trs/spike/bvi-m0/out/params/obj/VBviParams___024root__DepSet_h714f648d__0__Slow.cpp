// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviParams.h for the primary calling header

#include "VBviParams__pch.h"
#include "VBviParams___024root.h"

VL_ATTR_COLD void VBviParams___024root___eval_static(VBviParams___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___eval_static\n"); );
}

VL_ATTR_COLD void VBviParams___024root___eval_initial__TOP(VBviParams___024root* vlSelf);

VL_ATTR_COLD void VBviParams___024root___eval_initial(VBviParams___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___eval_initial\n"); );
    // Body
    VBviParams___024root___eval_initial__TOP(vlSelf);
}

VL_ATTR_COLD void VBviParams___024root___eval_initial__TOP(VBviParams___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___eval_initial__TOP\n"); );
    // Body
    VL_WRITEF("STR=hello RVAL=2.5\n");
    vlSelf->P_SINT = 0xfffffffbU;
    vlSelf->P_WIDE[0U] = 0x1234567U;
    vlSelf->P_WIDE[1U] = 0x89abcdefU;
    vlSelf->P_WIDE[2U] = 0x1234567U;
}

VL_ATTR_COLD void VBviParams___024root___eval_final(VBviParams___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___eval_final\n"); );
}

VL_ATTR_COLD void VBviParams___024root___eval_settle(VBviParams___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___eval_settle\n"); );
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviParams___024root___dump_triggers__act(VBviParams___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___dump_triggers__act\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VactTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
}
#endif  // VL_DEBUG

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviParams___024root___dump_triggers__nba(VBviParams___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___dump_triggers__nba\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VnbaTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviParams___024root___ctor_var_reset(VBviParams___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___ctor_var_reset\n"); );
    // Body
    vlSelf->CLK = 0;
    vlSelf->P_SINT = 0;
    VL_ZERO_RESET_W(96, vlSelf->P_WIDE);
}
