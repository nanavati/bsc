// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviXing.h for the primary calling header

#include "VBviXing__pch.h"
#include "VBviXing___024root.h"

VL_ATTR_COLD void VBviXing___024root___eval_static(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_static\n"); );
}

VL_ATTR_COLD void VBviXing___024root___eval_initial(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_initial\n"); );
    // Body
    vlSelf->__Vtrigprevexpr___TOP__SCLK__0 = vlSelf->SCLK;
    vlSelf->__Vtrigprevexpr___TOP__DCLK__0 = vlSelf->DCLK;
}

VL_ATTR_COLD void VBviXing___024root___eval_final(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_final\n"); );
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviXing___024root___dump_triggers__stl(VBviXing___024root* vlSelf);
#endif  // VL_DEBUG
VL_ATTR_COLD bool VBviXing___024root___eval_phase__stl(VBviXing___024root* vlSelf);

VL_ATTR_COLD void VBviXing___024root___eval_settle(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_settle\n"); );
    // Init
    IData/*31:0*/ __VstlIterCount;
    CData/*0:0*/ __VstlContinue;
    // Body
    __VstlIterCount = 0U;
    vlSelf->__VstlFirstIteration = 1U;
    __VstlContinue = 1U;
    while (__VstlContinue) {
        if (VL_UNLIKELY((0x64U < __VstlIterCount))) {
#ifdef VL_DEBUG
            VBviXing___024root___dump_triggers__stl(vlSelf);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviXing.v", 3, "", "Settle region did not converge.");
        }
        __VstlIterCount = ((IData)(1U) + __VstlIterCount);
        __VstlContinue = 0U;
        if (VBviXing___024root___eval_phase__stl(vlSelf)) {
            __VstlContinue = 1U;
        }
        vlSelf->__VstlFirstIteration = 0U;
    }
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviXing___024root___dump_triggers__stl(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___dump_triggers__stl\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VstlTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VstlTriggered.word(0U))) {
        VL_DBG_MSGF("         'stl' region trigger index 0 is active: Internal 'stl' trigger - first iteration\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviXing___024root___stl_sequent__TOP__0(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___stl_sequent__TOP__0\n"); );
    // Body
    vlSelf->SREG = vlSelf->BviXing__DOT__sreg;
    vlSelf->DREG = vlSelf->BviXing__DOT__dreg;
}

VL_ATTR_COLD void VBviXing___024root___eval_stl(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_stl\n"); );
    // Body
    if ((1ULL & vlSelf->__VstlTriggered.word(0U))) {
        VBviXing___024root___stl_sequent__TOP__0(vlSelf);
    }
}

VL_ATTR_COLD void VBviXing___024root___eval_triggers__stl(VBviXing___024root* vlSelf);

VL_ATTR_COLD bool VBviXing___024root___eval_phase__stl(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_phase__stl\n"); );
    // Init
    CData/*0:0*/ __VstlExecute;
    // Body
    VBviXing___024root___eval_triggers__stl(vlSelf);
    __VstlExecute = vlSelf->__VstlTriggered.any();
    if (__VstlExecute) {
        VBviXing___024root___eval_stl(vlSelf);
    }
    return (__VstlExecute);
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviXing___024root___dump_triggers__act(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___dump_triggers__act\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VactTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VactTriggered.word(0U))) {
        VL_DBG_MSGF("         'act' region trigger index 0 is active: @(posedge SCLK)\n");
    }
    if ((2ULL & vlSelf->__VactTriggered.word(0U))) {
        VL_DBG_MSGF("         'act' region trigger index 1 is active: @(posedge DCLK)\n");
    }
}
#endif  // VL_DEBUG

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviXing___024root___dump_triggers__nba(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___dump_triggers__nba\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VnbaTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 0 is active: @(posedge SCLK)\n");
    }
    if ((2ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 1 is active: @(posedge DCLK)\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviXing___024root___ctor_var_reset(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___ctor_var_reset\n"); );
    // Body
    vlSelf->SCLK = 0;
    vlSelf->DCLK = 0;
    vlSelf->RST_N = 0;
    vlSelf->EN_send = 0;
    vlSelf->s_din = 0;
    vlSelf->SREG = 0;
    vlSelf->DREG = 0;
    vlSelf->BviXing__DOT__sreg = 0;
    vlSelf->BviXing__DOT__dreg = 0;
    vlSelf->__Vtrigprevexpr___TOP__SCLK__0 = 0;
    vlSelf->__Vtrigprevexpr___TOP__DCLK__0 = 0;
}
