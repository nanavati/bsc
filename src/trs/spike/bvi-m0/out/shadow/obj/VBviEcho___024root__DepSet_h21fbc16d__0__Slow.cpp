// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviEcho.h for the primary calling header

#include "VBviEcho__pch.h"
#include "VBviEcho___024root.h"

VL_ATTR_COLD void VBviEcho___024root___eval_static(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___eval_static\n"); );
}

VL_ATTR_COLD void VBviEcho___024root___eval_initial(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___eval_initial\n"); );
    // Body
    vlSelf->__Vtrigprevexpr___TOP__CLK__0 = vlSelf->CLK;
}

VL_ATTR_COLD void VBviEcho___024root___eval_final(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___eval_final\n"); );
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviEcho___024root___dump_triggers__stl(VBviEcho___024root* vlSelf);
#endif  // VL_DEBUG
VL_ATTR_COLD bool VBviEcho___024root___eval_phase__stl(VBviEcho___024root* vlSelf);

VL_ATTR_COLD void VBviEcho___024root___eval_settle(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___eval_settle\n"); );
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
            VBviEcho___024root___dump_triggers__stl(vlSelf);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviEcho.v", 4, "", "Settle region did not converge.");
        }
        __VstlIterCount = ((IData)(1U) + __VstlIterCount);
        __VstlContinue = 0U;
        if (VBviEcho___024root___eval_phase__stl(vlSelf)) {
            __VstlContinue = 1U;
        }
        vlSelf->__VstlFirstIteration = 0U;
    }
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviEcho___024root___dump_triggers__stl(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___dump_triggers__stl\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VstlTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VstlTriggered.word(0U))) {
        VL_DBG_MSGF("         'stl' region trigger index 0 is active: Internal 'stl' trigger - first iteration\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviEcho___024root___stl_sequent__TOP__0(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___stl_sequent__TOP__0\n"); );
    // Body
    vlSelf->OUT = (0xffU & ((IData)(1U) + (IData)(vlSelf->IN)));
    vlSelf->LAST = vlSelf->BviEcho__DOT__last;
}

VL_ATTR_COLD void VBviEcho___024root___eval_stl(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___eval_stl\n"); );
    // Body
    if ((1ULL & vlSelf->__VstlTriggered.word(0U))) {
        VBviEcho___024root___stl_sequent__TOP__0(vlSelf);
    }
}

VL_ATTR_COLD void VBviEcho___024root___eval_triggers__stl(VBviEcho___024root* vlSelf);

VL_ATTR_COLD bool VBviEcho___024root___eval_phase__stl(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___eval_phase__stl\n"); );
    // Init
    CData/*0:0*/ __VstlExecute;
    // Body
    VBviEcho___024root___eval_triggers__stl(vlSelf);
    __VstlExecute = vlSelf->__VstlTriggered.any();
    if (__VstlExecute) {
        VBviEcho___024root___eval_stl(vlSelf);
    }
    return (__VstlExecute);
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviEcho___024root___dump_triggers__ico(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___dump_triggers__ico\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VicoTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VicoTriggered.word(0U))) {
        VL_DBG_MSGF("         'ico' region trigger index 0 is active: Internal 'ico' trigger - first iteration\n");
    }
}
#endif  // VL_DEBUG

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviEcho___024root___dump_triggers__act(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___dump_triggers__act\n"); );
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
VL_ATTR_COLD void VBviEcho___024root___dump_triggers__nba(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___dump_triggers__nba\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VnbaTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 0 is active: @(posedge CLK)\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviEcho___024root___ctor_var_reset(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___ctor_var_reset\n"); );
    // Body
    vlSelf->CLK = 0;
    vlSelf->RST_N = 0;
    vlSelf->EN = 0;
    vlSelf->IN = 0;
    vlSelf->OUT = 0;
    vlSelf->LAST = 0;
    vlSelf->BviEcho__DOT__last = 0;
    vlSelf->__Vtrigprevexpr___TOP__CLK__0 = 0;
}
