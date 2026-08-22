// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviXing.h for the primary calling header

#include "VBviXing__pch.h"

bool VBviXing___024root___trigger_anySet__act(const VlUnpacked<QData/*63:0*/, 1> &in) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___trigger_anySet__act\n"); );
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

void VBviXing___024root___trigger_orInto__act_vec_vec(VlUnpacked<QData/*63:0*/, 1> &out, const VlUnpacked<QData/*63:0*/, 1> &in) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___trigger_orInto__act_vec_vec\n"); );
    // Locals
    IData/*31:0*/ n;
    // Body
    n = 0U;
    do {
        out[n] = (out[n] | in[n]);
        n = ((IData)(1U) + n);
    } while ((0U >= n));
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviXing___024root___dump_triggers__act(const VlUnpacked<QData/*63:0*/, 1> &triggers, const std::string &tag);
#endif  // VL_DEBUG

bool VBviXing___024root___eval_phase__act(VBviXing___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_phase__act\n"); );
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    {
        // Inlined CFunc: _eval_triggers_vec__act
        vlSelfRef.__VactTriggered[0U] = (QData)((IData)(
                                                        ((((IData)(vlSelfRef.DCLK) 
                                                           & (~ (IData)(vlSelfRef.__Vtrigprevexpr___TOP__DCLK__0))) 
                                                          << 1U) 
                                                         | ((IData)(vlSelfRef.SCLK) 
                                                            & (~ (IData)(vlSelfRef.__Vtrigprevexpr___TOP__SCLK__0))))));
        vlSelfRef.__Vtrigprevexpr___TOP__SCLK__0 = vlSelfRef.SCLK;
        vlSelfRef.__Vtrigprevexpr___TOP__DCLK__0 = vlSelfRef.DCLK;
    }
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VBviXing___024root___dump_triggers__act(vlSelfRef.__VactTriggered, "act"s);
    }
#endif
    VBviXing___024root___trigger_orInto__act_vec_vec(vlSelfRef.__VnbaTriggered, vlSelfRef.__VactTriggered);
    return (0U);
}

void VBviXing___024root___trigger_clear__act(VlUnpacked<QData/*63:0*/, 1> &out) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___trigger_clear__act\n"); );
    // Locals
    IData/*31:0*/ n;
    // Body
    n = 0U;
    do {
        out[n] = 0ULL;
        n = ((IData)(1U) + n);
    } while ((1U > n));
}

bool VBviXing___024root___eval_phase__nba(VBviXing___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_phase__nba\n"); );
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*0:0*/ __VnbaExecute;
    // Body
    __VnbaExecute = VBviXing___024root___trigger_anySet__act(vlSelfRef.__VnbaTriggered);
    if (__VnbaExecute) {
        {
            // Inlined CFunc: _eval_nba
            if ((2ULL & vlSelfRef.__VnbaTriggered[0U])) {
                {
                    // Inlined CFunc: _nba_sequent__TOP__0
                    vlSelfRef.BviXing__DOT__dreg = 
                        ((IData)(vlSelfRef.RST_N) ? (IData)(vlSelfRef.BviXing__DOT__sreg)
                          : 0U);
                    vlSelfRef.DREG = vlSelfRef.BviXing__DOT__dreg;
                }
            }
            if ((1ULL & vlSelfRef.__VnbaTriggered[0U])) {
                {
                    // Inlined CFunc: _nba_sequent__TOP__1
                    if (vlSelfRef.RST_N) {
                        if (vlSelfRef.EN_send) {
                            vlSelfRef.BviXing__DOT__sreg 
                                = vlSelfRef.s_din;
                        }
                    } else {
                        vlSelfRef.BviXing__DOT__sreg = 0U;
                    }
                    vlSelfRef.SREG = vlSelfRef.BviXing__DOT__sreg;
                }
            }
        }
        VBviXing___024root___trigger_clear__act(vlSelfRef.__VnbaTriggered);
    }
    return (__VnbaExecute);
}

void VBviXing___024root___eval(VBviXing___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval\n"); );
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    IData/*31:0*/ __VnbaIterCount;
    // Body
    __VnbaIterCount = 0U;
    do {
        if (VL_UNLIKELY(((0x00002710U < __VnbaIterCount)))) {
#ifdef VL_DEBUG
            VBviXing___024root___dump_triggers__act(vlSelfRef.__VnbaTriggered, "nba"s);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviXing.v", 3, "", "DIDNOTCONVERGE: NBA region did not converge after '--converge-limit' of 10000 tries");
        }
        __VnbaIterCount = ((IData)(1U) + __VnbaIterCount);
        vlSelfRef.__VactIterCount = 0U;
        do {
            if (VL_UNLIKELY(((0x00002710U < vlSelfRef.__VactIterCount)))) {
#ifdef VL_DEBUG
                VBviXing___024root___dump_triggers__act(vlSelfRef.__VactTriggered, "act"s);
#endif
                VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviXing.v", 3, "", "DIDNOTCONVERGE: Active region did not converge after '--converge-limit' of 10000 tries");
            }
            vlSelfRef.__VactIterCount = ((IData)(1U) 
                                         + vlSelfRef.__VactIterCount);
            vlSelfRef.__VactPhaseResult = VBviXing___024root___eval_phase__act(vlSelf);
        } while (vlSelfRef.__VactPhaseResult);
        vlSelfRef.__VnbaPhaseResult = VBviXing___024root___eval_phase__nba(vlSelf);
    } while (vlSelfRef.__VnbaPhaseResult);
}

#ifdef VL_DEBUG
void VBviXing___024root___eval_debug_assertions(VBviXing___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_debug_assertions\n"); );
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    if (VL_UNLIKELY(((vlSelfRef.SCLK & 0xfeU)))) {
        Verilated::overWidthError("SCLK");
    }
    if (VL_UNLIKELY(((vlSelfRef.DCLK & 0xfeU)))) {
        Verilated::overWidthError("DCLK");
    }
    if (VL_UNLIKELY(((vlSelfRef.RST_N & 0xfeU)))) {
        Verilated::overWidthError("RST_N");
    }
    if (VL_UNLIKELY(((vlSelfRef.EN_send & 0xfeU)))) {
        Verilated::overWidthError("EN_send");
    }
}
#endif  // VL_DEBUG
