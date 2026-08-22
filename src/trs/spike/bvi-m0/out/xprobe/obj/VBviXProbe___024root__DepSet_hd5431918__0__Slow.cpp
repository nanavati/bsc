// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviXProbe.h for the primary calling header

#include "VBviXProbe__pch.h"
#include "VBviXProbe___024root.h"

VL_ATTR_COLD void VBviXProbe___024root___eval_static(VBviXProbe___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXProbe__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXProbe___024root___eval_static\n"); );
}

VL_ATTR_COLD void VBviXProbe___024root___eval_initial__TOP(VBviXProbe___024root* vlSelf);

VL_ATTR_COLD void VBviXProbe___024root___eval_initial(VBviXProbe___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXProbe__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXProbe___024root___eval_initial\n"); );
    // Body
    VBviXProbe___024root___eval_initial__TOP(vlSelf);
    vlSelf->__Vtrigprevexpr___TOP__CLK__0 = vlSelf->CLK;
}

VL_ATTR_COLD void VBviXProbe___024root___eval_initial__TOP(VBviXProbe___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXProbe__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXProbe___024root___eval_initial__TOP\n"); );
    // Body
    vlSelf->RDYX = 0U;
}

VL_ATTR_COLD void VBviXProbe___024root___eval_final(VBviXProbe___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXProbe__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXProbe___024root___eval_final\n"); );
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviXProbe___024root___dump_triggers__stl(VBviXProbe___024root* vlSelf);
#endif  // VL_DEBUG
VL_ATTR_COLD bool VBviXProbe___024root___eval_phase__stl(VBviXProbe___024root* vlSelf);

VL_ATTR_COLD void VBviXProbe___024root___eval_settle(VBviXProbe___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXProbe__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXProbe___024root___eval_settle\n"); );
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
            VBviXProbe___024root___dump_triggers__stl(vlSelf);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviXProbe.v", 4, "", "Settle region did not converge.");
        }
        __VstlIterCount = ((IData)(1U) + __VstlIterCount);
        __VstlContinue = 0U;
        if (VBviXProbe___024root___eval_phase__stl(vlSelf)) {
            __VstlContinue = 1U;
        }
        vlSelf->__VstlFirstIteration = 0U;
    }
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviXProbe___024root___dump_triggers__stl(VBviXProbe___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXProbe__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXProbe___024root___dump_triggers__stl\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VstlTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VstlTriggered.word(0U))) {
        VL_DBG_MSGF("         'stl' region trigger index 0 is active: Internal 'stl' trigger - first iteration\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviXProbe___024root___stl_sequent__TOP__0(VBviXProbe___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXProbe__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXProbe___024root___stl_sequent__TOP__0\n"); );
    // Body
    vlSelf->Q = vlSelf->BviXProbe__DOT__q;
}

VL_ATTR_COLD void VBviXProbe___024root___eval_stl(VBviXProbe___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXProbe__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXProbe___024root___eval_stl\n"); );
    // Body
    if ((1ULL & vlSelf->__VstlTriggered.word(0U))) {
        VBviXProbe___024root___stl_sequent__TOP__0(vlSelf);
    }
}

VL_ATTR_COLD void VBviXProbe___024root___eval_triggers__stl(VBviXProbe___024root* vlSelf);

VL_ATTR_COLD bool VBviXProbe___024root___eval_phase__stl(VBviXProbe___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXProbe__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXProbe___024root___eval_phase__stl\n"); );
    // Init
    CData/*0:0*/ __VstlExecute;
    // Body
    VBviXProbe___024root___eval_triggers__stl(vlSelf);
    __VstlExecute = vlSelf->__VstlTriggered.any();
    if (__VstlExecute) {
        VBviXProbe___024root___eval_stl(vlSelf);
    }
    return (__VstlExecute);
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviXProbe___024root___dump_triggers__act(VBviXProbe___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXProbe__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXProbe___024root___dump_triggers__act\n"); );
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
VL_ATTR_COLD void VBviXProbe___024root___dump_triggers__nba(VBviXProbe___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXProbe__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXProbe___024root___dump_triggers__nba\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VnbaTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 0 is active: @(posedge CLK)\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviXProbe___024root___ctor_var_reset(VBviXProbe___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXProbe__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXProbe___024root___ctor_var_reset\n"); );
    // Body
    vlSelf->CLK = 0;
    vlSelf->RST_N = 0;
    vlSelf->RDYX = 0;
    vlSelf->Q = 0;
    vlSelf->BviXProbe__DOT__q = 0;
    vlSelf->__Vtrigprevexpr___TOP__CLK__0 = 0;
}
