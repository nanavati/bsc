// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviFatal.h for the primary calling header

#include "VBviFatal__pch.h"

VL_ATTR_COLD void VBviFatal___024root___eval_static(VBviFatal___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval_static\n"); );
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.__Vtrigprevexpr___TOP__CLK__0 = vlSelfRef.CLK;
}

VL_ATTR_COLD void VBviFatal___024root___eval_initial(VBviFatal___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval_initial\n"); );
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    {
        // Inlined CFunc: _eval_initial__TOP
        vlSelfRef.OUT = 7U;
    }
}

VL_ATTR_COLD void VBviFatal___024root___eval_final(VBviFatal___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval_final\n"); );
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

VL_ATTR_COLD void VBviFatal___024root___eval_settle(VBviFatal___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval_settle\n"); );
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

bool VBviFatal___024root___trigger_anySet__act(const VlUnpacked<QData/*63:0*/, 1> &in);

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviFatal___024root___dump_triggers__act(const VlUnpacked<QData/*63:0*/, 1> &triggers, const std::string &tag) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___dump_triggers__act\n"); );
    // Body
    if ((1U & (~ (IData)(VBviFatal___024root___trigger_anySet__act(triggers))))) {
        VL_DBG_MSGS("         No '" + tag + "' region triggers active\n");
    }
    if ((1U & (IData)(triggers[0U]))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 0 is active: @(posedge CLK)\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviFatal___024root___ctor_var_reset(VBviFatal___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___ctor_var_reset\n"); );
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelf->CLK = 0;
    vlSelf->RST_N = 0;
    vlSelf->EN_go = 0;
    vlSelf->OUT = 0;
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->__VactTriggered[__Vi0] = 0;
    }
    vlSelf->__Vtrigprevexpr___TOP__CLK__0 = 0;
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->__VnbaTriggered[__Vi0] = 0;
    }
}
