// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviXing.h for the primary calling header

#include "VBviXing__pch.h"

VL_ATTR_COLD void VBviXing___024root___eval_static(VBviXing___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_static\n"); );
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.__Vtrigprevexpr___TOP__SCLK__0 = vlSelfRef.SCLK;
    vlSelfRef.__Vtrigprevexpr___TOP__DCLK__0 = vlSelfRef.DCLK;
}

VL_ATTR_COLD void VBviXing___024root___eval_initial(VBviXing___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_initial\n"); );
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

VL_ATTR_COLD void VBviXing___024root___eval_final(VBviXing___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_final\n"); );
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviXing___024root___dump_triggers__stl(const VlUnpacked<QData/*63:0*/, 1> &triggers, const std::string &tag);
#endif  // VL_DEBUG
VL_ATTR_COLD bool VBviXing___024root___eval_phase__stl(VBviXing___024root* vlSelf);

VL_ATTR_COLD void VBviXing___024root___eval_settle(VBviXing___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_settle\n"); );
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    IData/*31:0*/ __VstlIterCount;
    // Body
    __VstlIterCount = 0U;
    vlSelfRef.__VstlFirstIteration = 1U;
    do {
        if (VL_UNLIKELY(((0x00002710U < __VstlIterCount)))) {
#ifdef VL_DEBUG
            VBviXing___024root___dump_triggers__stl(vlSelfRef.__VstlTriggered, "stl"s);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviXing.v", 3, "", "DIDNOTCONVERGE: Settle region did not converge after '--converge-limit' of 10000 tries");
        }
        __VstlIterCount = ((IData)(1U) + __VstlIterCount);
        vlSelfRef.__VstlPhaseResult = VBviXing___024root___eval_phase__stl(vlSelf);
        vlSelfRef.__VstlFirstIteration = 0U;
    } while (vlSelfRef.__VstlPhaseResult);
}

VL_ATTR_COLD bool VBviXing___024root___trigger_anySet__stl(const VlUnpacked<QData/*63:0*/, 1> &in);

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviXing___024root___dump_triggers__stl(const VlUnpacked<QData/*63:0*/, 1> &triggers, const std::string &tag) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___dump_triggers__stl\n"); );
    // Body
    if ((1U & (~ (IData)(VBviXing___024root___trigger_anySet__stl(triggers))))) {
        VL_DBG_MSGS("         No '" + tag + "' region triggers active\n");
    }
    if ((1U & (IData)(triggers[0U]))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 0 is active: Internal 'stl' trigger - first iteration\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD bool VBviXing___024root___trigger_anySet__stl(const VlUnpacked<QData/*63:0*/, 1> &in) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___trigger_anySet__stl\n"); );
    // Locals
    IData/*31:0*/ n;
    // Body
    n = 0U;
    do {
        if (in[n]) {
            return (1U);
        }
        n = ((IData)(1U) + n);
    } while ((1U > n));
    return (0U);
}

VL_ATTR_COLD bool VBviXing___024root___eval_phase__stl(VBviXing___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_phase__stl\n"); );
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*0:0*/ __VstlExecute;
    // Body
    {
        // Inlined CFunc: _eval_triggers_vec__stl
        vlSelfRef.__VstlTriggered[0U] = ((0xfffffffffffffffeULL 
                                          & vlSelfRef.__VstlTriggered[0U]) 
                                         | (IData)((IData)(vlSelfRef.__VstlFirstIteration)));
    }
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VBviXing___024root___dump_triggers__stl(vlSelfRef.__VstlTriggered, "stl"s);
    }
#endif
    __VstlExecute = VBviXing___024root___trigger_anySet__stl(vlSelfRef.__VstlTriggered);
    if (__VstlExecute) {
        {
            // Inlined CFunc: _eval_stl
            if ((1ULL & vlSelfRef.__VstlTriggered[0U])) {
                {
                    // Inlined CFunc: _stl_sequent__TOP__0
                    vlSelfRef.SREG = vlSelfRef.BviXing__DOT__sreg;
                    vlSelfRef.DREG = vlSelfRef.BviXing__DOT__dreg;
                }
            }
        }
    }
    return (__VstlExecute);
}

bool VBviXing___024root___trigger_anySet__act(const VlUnpacked<QData/*63:0*/, 1> &in);

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviXing___024root___dump_triggers__act(const VlUnpacked<QData/*63:0*/, 1> &triggers, const std::string &tag) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___dump_triggers__act\n"); );
    // Body
    if ((1U & (~ (IData)(VBviXing___024root___trigger_anySet__act(triggers))))) {
        VL_DBG_MSGS("         No '" + tag + "' region triggers active\n");
    }
    if ((1U & (IData)(triggers[0U]))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 0 is active: @(posedge SCLK)\n");
    }
    if ((1U & (IData)((triggers[0U] >> 1U)))) {
        VL_DBG_MSGS("         '" + tag + "' region trigger index 1 is active: @(posedge DCLK)\n");
    }
}
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviXing___024root___ctor_var_reset(VBviXing___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___ctor_var_reset\n"); );
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
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
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->__VstlTriggered[__Vi0] = 0;
    }
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->__VactTriggered[__Vi0] = 0;
    }
    vlSelf->__Vtrigprevexpr___TOP__SCLK__0 = 0;
    vlSelf->__Vtrigprevexpr___TOP__DCLK__0 = 0;
    for (int __Vi0 = 0; __Vi0 < 1; ++__Vi0) {
        vlSelf->__VnbaTriggered[__Vi0] = 0;
    }
}
