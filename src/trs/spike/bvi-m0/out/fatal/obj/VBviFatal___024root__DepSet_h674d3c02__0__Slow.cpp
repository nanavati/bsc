// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviFatal.h for the primary calling header

#include "VBviFatal__pch.h"
#include "VBviFatal___024root.h"

VL_ATTR_COLD void VBviFatal___024root___eval_static(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval_static\n"); );
}

VL_ATTR_COLD void VBviFatal___024root___eval_initial__TOP(VBviFatal___024root* vlSelf);

VL_ATTR_COLD void VBviFatal___024root___eval_initial(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval_initial\n"); );
    // Body
    VBviFatal___024root___eval_initial__TOP(vlSelf);
    vlSelf->__Vtrigprevexpr___TOP__CLK__0 = vlSelf->CLK;
}

VL_ATTR_COLD void VBviFatal___024root___eval_initial__TOP(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval_initial__TOP\n"); );
    // Body
    vlSelf->OUT = 7U;
}

VL_ATTR_COLD void VBviFatal___024root___eval_final(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval_final\n"); );
}

VL_ATTR_COLD void VBviFatal___024root___eval_settle(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval_settle\n"); );
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviFatal___024root___dump_triggers__act(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___dump_triggers__act\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VactTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VactTriggered.word(0U))) {
        VL_DBG_MSGF("         'act' region trigger index 0 is active: @(posedge CLK)\n");
    }
}
#endif  // VL_DEBUG

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviFatal___024root___dump_triggers__nba(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___dump_triggers__nba\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VnbaTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 0 is active: @(posedge CLK)\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviFatal___024root___ctor_var_reset(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___ctor_var_reset\n"); );
    // Body
    vlSelf->CLK = 0;
    vlSelf->RST_N = 0;
    vlSelf->EN_go = 0;
    vlSelf->OUT = 0;
    vlSelf->__Vtrigprevexpr___TOP__CLK__0 = 0;
}
