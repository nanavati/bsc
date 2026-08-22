// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviViolator.h for the primary calling header

#include "VBviViolator__pch.h"

bool VBviViolator___024root___trigger_anySet__act(const VlUnpacked<QData/*63:0*/, 1> &in) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviViolator___024root___trigger_anySet__act\n"); );
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

void VBviViolator___024root___trigger_orInto__act_vec_vec(VlUnpacked<QData/*63:0*/, 1> &out, const VlUnpacked<QData/*63:0*/, 1> &in) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviViolator___024root___trigger_orInto__act_vec_vec\n"); );
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
VL_ATTR_COLD void VBviViolator___024root___dump_triggers__act(const VlUnpacked<QData/*63:0*/, 1> &triggers, const std::string &tag);
#endif  // VL_DEBUG

bool VBviViolator___024root___eval_phase__act(VBviViolator___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviViolator___024root___eval_phase__act\n"); );
    VBviViolator__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    {
        // Inlined CFunc: _eval_triggers_vec__act
        vlSelfRef.__VactTriggered[0U] = (QData)((IData)(
                                                        (1U 
                                                         & ((IData)(vlSelfRef.put_x) 
                                                            & (~ (IData)(vlSelfRef.__Vtrigprevexpr_h5367cfe6__0))))));
        vlSelfRef.__Vtrigprevexpr_h5367cfe6__0 = (1U 
                                                  & (IData)(vlSelfRef.put_x));
    }
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VBviViolator___024root___dump_triggers__act(vlSelfRef.__VactTriggered, "act"s);
    }
#endif
    VBviViolator___024root___trigger_orInto__act_vec_vec(vlSelfRef.__VnbaTriggered, vlSelfRef.__VactTriggered);
    return (0U);
}

void VBviViolator___024root___trigger_clear__act(VlUnpacked<QData/*63:0*/, 1> &out) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviViolator___024root___trigger_clear__act\n"); );
    // Locals
    IData/*31:0*/ n;
    // Body
    n = 0U;
    do {
        out[n] = 0ULL;
        n = ((IData)(1U) + n);
    } while ((1U > n));
}

bool VBviViolator___024root___eval_phase__nba(VBviViolator___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviViolator___024root___eval_phase__nba\n"); );
    VBviViolator__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*0:0*/ __VnbaExecute;
    // Body
    __VnbaExecute = VBviViolator___024root___trigger_anySet__act(vlSelfRef.__VnbaTriggered);
    if (__VnbaExecute) {
        {
            // Inlined CFunc: _eval_nba
            if ((1ULL & vlSelfRef.__VnbaTriggered[0U])) {
                {
                    // Inlined CFunc: _nba_sequent__TOP__0
                    vlSelfRef.BviViolator__DOT__cnt 
                        = (0x000000ffU & ((IData)(1U) 
                                          + (IData)(vlSelfRef.BviViolator__DOT__cnt)));
                    vlSelfRef.COUNT = vlSelfRef.BviViolator__DOT__cnt;
                }
            }
        }
        VBviViolator___024root___trigger_clear__act(vlSelfRef.__VnbaTriggered);
    }
    return (__VnbaExecute);
}

void VBviViolator___024root___eval(VBviViolator___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviViolator___024root___eval\n"); );
    VBviViolator__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    IData/*31:0*/ __VnbaIterCount;
    // Body
    __VnbaIterCount = 0U;
    do {
        if (VL_UNLIKELY(((0x00002710U < __VnbaIterCount)))) {
#ifdef VL_DEBUG
            VBviViolator___024root___dump_triggers__act(vlSelfRef.__VnbaTriggered, "nba"s);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviViolator.v", 5, "", "DIDNOTCONVERGE: NBA region did not converge after '--converge-limit' of 10000 tries");
        }
        __VnbaIterCount = ((IData)(1U) + __VnbaIterCount);
        vlSelfRef.__VactIterCount = 0U;
        do {
            if (VL_UNLIKELY(((0x00002710U < vlSelfRef.__VactIterCount)))) {
#ifdef VL_DEBUG
                VBviViolator___024root___dump_triggers__act(vlSelfRef.__VactTriggered, "act"s);
#endif
                VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviViolator.v", 5, "", "DIDNOTCONVERGE: Active region did not converge after '--converge-limit' of 10000 tries");
            }
            vlSelfRef.__VactIterCount = ((IData)(1U) 
                                         + vlSelfRef.__VactIterCount);
            vlSelfRef.__VactPhaseResult = VBviViolator___024root___eval_phase__act(vlSelf);
        } while (vlSelfRef.__VactPhaseResult);
        vlSelfRef.__VnbaPhaseResult = VBviViolator___024root___eval_phase__nba(vlSelf);
    } while (vlSelfRef.__VnbaPhaseResult);
}

#ifdef VL_DEBUG
void VBviViolator___024root___eval_debug_assertions(VBviViolator___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviViolator___024root___eval_debug_assertions\n"); );
    VBviViolator__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    if (VL_UNLIKELY(((vlSelfRef.CLK & 0xfeU)))) {
        Verilated::overWidthError("CLK");
    }
    if (VL_UNLIKELY(((vlSelfRef.RST_N & 0xfeU)))) {
        Verilated::overWidthError("RST_N");
    }
    if (VL_UNLIKELY(((vlSelfRef.EN_put & 0xfeU)))) {
        Verilated::overWidthError("EN_put");
    }
}
#endif  // VL_DEBUG
