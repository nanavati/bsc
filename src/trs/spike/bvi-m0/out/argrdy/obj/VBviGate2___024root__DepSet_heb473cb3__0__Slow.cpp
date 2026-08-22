// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviGate2.h for the primary calling header

#include "VBviGate2__pch.h"
#include "VBviGate2___024root.h"

VL_ATTR_COLD void VBviGate2___024root___eval_static(VBviGate2___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviGate2__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviGate2___024root___eval_static\n"); );
}

VL_ATTR_COLD void VBviGate2___024root___eval_initial(VBviGate2___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviGate2__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviGate2___024root___eval_initial\n"); );
    // Body
    vlSelf->__Vtrigprevexpr___TOP__CLK__0 = vlSelf->CLK;
}

VL_ATTR_COLD void VBviGate2___024root___eval_final(VBviGate2___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviGate2__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviGate2___024root___eval_final\n"); );
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviGate2___024root___dump_triggers__stl(VBviGate2___024root* vlSelf);
#endif  // VL_DEBUG
VL_ATTR_COLD bool VBviGate2___024root___eval_phase__stl(VBviGate2___024root* vlSelf);

VL_ATTR_COLD void VBviGate2___024root___eval_settle(VBviGate2___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviGate2__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviGate2___024root___eval_settle\n"); );
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
            VBviGate2___024root___dump_triggers__stl(vlSelf);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviGate2.v", 6, "", "Settle region did not converge.");
        }
        __VstlIterCount = ((IData)(1U) + __VstlIterCount);
        __VstlContinue = 0U;
        if (VBviGate2___024root___eval_phase__stl(vlSelf)) {
            __VstlContinue = 1U;
        }
        vlSelf->__VstlFirstIteration = 0U;
    }
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviGate2___024root___dump_triggers__stl(VBviGate2___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviGate2__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviGate2___024root___dump_triggers__stl\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VstlTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VstlTriggered.word(0U))) {
        VL_DBG_MSGF("         'stl' region trigger index 0 is active: Internal 'stl' trigger - first iteration\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviGate2___024root___stl_sequent__TOP__0(VBviGate2___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviGate2__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviGate2___024root___stl_sequent__TOP__0\n"); );
    // Body
    vlSelf->STORED = vlSelf->BviGate2__DOT__stored;
    vlSelf->RDY_put = ((~ (IData)(vlSelf->put_x)) & (IData)(vlSelf->RST_N));
}

VL_ATTR_COLD void VBviGate2___024root___eval_stl(VBviGate2___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviGate2__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviGate2___024root___eval_stl\n"); );
    // Body
    if ((1ULL & vlSelf->__VstlTriggered.word(0U))) {
        VBviGate2___024root___stl_sequent__TOP__0(vlSelf);
    }
}

VL_ATTR_COLD void VBviGate2___024root___eval_triggers__stl(VBviGate2___024root* vlSelf);

VL_ATTR_COLD bool VBviGate2___024root___eval_phase__stl(VBviGate2___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviGate2__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviGate2___024root___eval_phase__stl\n"); );
    // Init
    CData/*0:0*/ __VstlExecute;
    // Body
    VBviGate2___024root___eval_triggers__stl(vlSelf);
    __VstlExecute = vlSelf->__VstlTriggered.any();
    if (__VstlExecute) {
        VBviGate2___024root___eval_stl(vlSelf);
    }
    return (__VstlExecute);
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviGate2___024root___dump_triggers__ico(VBviGate2___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviGate2__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviGate2___024root___dump_triggers__ico\n"); );
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
VL_ATTR_COLD void VBviGate2___024root___dump_triggers__act(VBviGate2___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviGate2__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviGate2___024root___dump_triggers__act\n"); );
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
VL_ATTR_COLD void VBviGate2___024root___dump_triggers__nba(VBviGate2___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviGate2__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviGate2___024root___dump_triggers__nba\n"); );
    // Body
    if ((1U & (~ (IData)(vlSelf->__VnbaTriggered.any())))) {
        VL_DBG_MSGF("         No triggers active\n");
    }
    if ((1ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VL_DBG_MSGF("         'nba' region trigger index 0 is active: @(posedge CLK)\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviGate2___024root___ctor_var_reset(VBviGate2___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviGate2__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviGate2___024root___ctor_var_reset\n"); );
    // Body
    vlSelf->CLK = 0;
    vlSelf->RST_N = 0;
    vlSelf->EN_put = 0;
    vlSelf->put_x = 0;
    vlSelf->RDY_put = 0;
    vlSelf->STORED = 0;
    vlSelf->BviGate2__DOT__stored = 0;
    vlSelf->__Vtrigprevexpr___TOP__CLK__0 = 0;
}
