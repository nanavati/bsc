// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviCounter.h for the primary calling header

#include "VBviCounter__pch.h"
#include "VBviCounter___024root.h"

VL_ATTR_COLD void VBviCounter___024root___eval_static(VBviCounter___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviCounter__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviCounter___024root___eval_static\n"); );
}

VL_ATTR_COLD void VBviCounter___024root___eval_initial(VBviCounter___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviCounter__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviCounter___024root___eval_initial\n"); );
    // Body
    vlSelf->__Vtrigprevexpr___TOP__CLK__0 = vlSelf->CLK;
}

VL_ATTR_COLD void VBviCounter___024root___eval_final(VBviCounter___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviCounter__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviCounter___024root___eval_final\n"); );
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviCounter___024root___dump_triggers__stl(VBviCounter___024root* vlSelf);
#endif  // VL_DEBUG
VL_ATTR_COLD bool VBviCounter___024root___eval_phase__stl(VBviCounter___024root* vlSelf);

VL_ATTR_COLD void VBviCounter___024root___eval_settle(VBviCounter___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviCounter__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviCounter___024root___eval_settle\n"); );
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
            VBviCounter___024root___dump_triggers__stl(vlSelf);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviCounter.v", 4, "", "Settle region did not converge.");
        }
        __VstlIterCount = ((IData)(1U) + __VstlIterCount);
        __VstlContinue = 0U;
        if (VBviCounter___024root___eval_phase__stl(vlSelf)) {
            __VstlContinue = 1U;
        }
        vlSelf->__VstlFirstIteration = 0U;
    }
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviCounter___024root___dump_triggers__stl(VBviCounter___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviCounter__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviCounter___024root___dump_triggers__stl\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VstlTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VstlTriggered.word(0U))) {
        VL_DBG_MSGF("         'stl' region trigger index 0 is active: Internal 'stl' trigger - first iteration\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviCounter___024root___stl_sequent__TOP__0(VBviCounter___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviCounter__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviCounter___024root___stl_sequent__TOP__0\n"); );
    // Body
    vlSelf->RDY_bump = vlSelf->RST_N;
    vlSelf->count = vlSelf->BviCounter__DOT__c;
}

VL_ATTR_COLD void VBviCounter___024root___eval_stl(VBviCounter___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviCounter__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviCounter___024root___eval_stl\n"); );
    // Body
    if ((1ULL & vlSelf->__VstlTriggered.word(0U))) {
        VBviCounter___024root___stl_sequent__TOP__0(vlSelf);
    }
}

VL_ATTR_COLD void VBviCounter___024root___eval_triggers__stl(VBviCounter___024root* vlSelf);

VL_ATTR_COLD bool VBviCounter___024root___eval_phase__stl(VBviCounter___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviCounter__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviCounter___024root___eval_phase__stl\n"); );
    // Init
    CData/*0:0*/ __VstlExecute;
    // Body
    VBviCounter___024root___eval_triggers__stl(vlSelf);
    __VstlExecute = vlSelf->__VstlTriggered.any();
    if (__VstlExecute) {
        VBviCounter___024root___eval_stl(vlSelf);
    }
    return (__VstlExecute);
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviCounter___024root___dump_triggers__ico(VBviCounter___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviCounter__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviCounter___024root___dump_triggers__ico\n"); );
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
VL_ATTR_COLD void VBviCounter___024root___dump_triggers__act(VBviCounter___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviCounter__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviCounter___024root___dump_triggers__act\n"); );
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
VL_ATTR_COLD void VBviCounter___024root___dump_triggers__nba(VBviCounter___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviCounter__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviCounter___024root___dump_triggers__nba\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VnbaTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 0 is active: @(posedge CLK)\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviCounter___024root___ctor_var_reset(VBviCounter___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviCounter__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviCounter___024root___ctor_var_reset\n"); );
    // Body
    vlSelf->CLK = 0;
    vlSelf->RST_N = 0;
    vlSelf->EN_bump = 0;
    vlSelf->bump_amt = 0;
    vlSelf->count = 0;
    vlSelf->RDY_bump = 0;
    vlSelf->BviCounter__DOT__c = 0;
    vlSelf->__Vtrigprevexpr___TOP__CLK__0 = 0;
}
