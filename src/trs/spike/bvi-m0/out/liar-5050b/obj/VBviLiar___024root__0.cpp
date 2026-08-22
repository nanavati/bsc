// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviLiar.h for the primary calling header

#include "VBviLiar__pch.h"

bool VBviLiar___024root___trigger_anySet__ico(const VlUnpacked<QData/*63:0*/, 2> &in) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___trigger_anySet__ico\n"); );
    // Locals
    IData/*31:0*/ n;
    // Body
    n = 0U;
    do {
        if (in[n]) {
            return (1U);
        }
        n = ((IData)(1U) + n);
    } while ((2U > n));
    return (0U);
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviLiar___024root___dump_triggers__ico(const VlUnpacked<QData/*63:0*/, 2> &triggers, const std::string &tag);
#endif  // VL_DEBUG

bool VBviLiar___024root___eval_phase__ico(VBviLiar___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___eval_phase__ico\n"); );
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*0:0*/ __VicoExecute;
    // Body
    {
        // Inlined CFunc: _eval_triggers_vec__ico
        vlSelfRef.__VicoTriggered[0U] = (QData)((IData)(
                                                        (((((IData)(vlSelfRef.put_x) 
                                                            != (IData)(vlSelfRef.__Vtrigprevexpr___TOP__put_x__0)) 
                                                           << 3U) 
                                                          | (((IData)(vlSelfRef.EN_put) 
                                                              != (IData)(vlSelfRef.__Vtrigprevexpr___TOP__EN_put__0)) 
                                                             << 2U)) 
                                                         | ((((IData)(vlSelfRef.RST_N) 
                                                              != (IData)(vlSelfRef.__Vtrigprevexpr___TOP__RST_N__0)) 
                                                             << 1U) 
                                                            | ((IData)(vlSelfRef.CLK) 
                                                               != (IData)(vlSelfRef.__Vtrigprevexpr___TOP__CLK__0))))));
        vlSelfRef.__Vtrigprevexpr___TOP__CLK__0 = vlSelfRef.CLK;
        vlSelfRef.__Vtrigprevexpr___TOP__RST_N__0 = vlSelfRef.RST_N;
        vlSelfRef.__Vtrigprevexpr___TOP__EN_put__0 
            = vlSelfRef.EN_put;
        vlSelfRef.__Vtrigprevexpr___TOP__put_x__0 = vlSelfRef.put_x;
        if (VL_UNLIKELY(((1U & (~ (IData)(vlSelfRef.__VicoDidInit)))))) {
            vlSelfRef.__VicoDidInit = 1U;
            vlSelfRef.__VicoTriggered[0U] = (1ULL | vlSelfRef.__VicoTriggered[0U]);
            vlSelfRef.__VicoTriggered[0U] = (2ULL | vlSelfRef.__VicoTriggered[0U]);
            vlSelfRef.__VicoTriggered[0U] = (4ULL | vlSelfRef.__VicoTriggered[0U]);
            vlSelfRef.__VicoTriggered[0U] = (8ULL | vlSelfRef.__VicoTriggered[0U]);
        }
    }
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VBviLiar___024root___dump_triggers__ico(vlSelfRef.__VicoTriggered, "ico"s);
    }
#endif
    __VicoExecute = VBviLiar___024root___trigger_anySet__ico(vlSelfRef.__VicoTriggered);
    if (__VicoExecute) {
        {
            // Inlined CFunc: _eval_ico
            if ((8ULL & vlSelfRef.__VicoTriggered[0U])) {
                {
                    // Inlined CFunc: _ico_sequent__TOP__0
                    vlSelfRef.PEEK = ((IData)(vlSelfRef.put_x) 
                                      ^ (IData)(vlSelfRef.BviLiar__DOT__stored));
                }
            }
        }
    }
    return (__VicoExecute);
}

bool VBviLiar___024root___trigger_anySet__act(const VlUnpacked<QData/*63:0*/, 1> &in) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___trigger_anySet__act\n"); );
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

void VBviLiar___024root___trigger_orInto__act_vec_vec(VlUnpacked<QData/*63:0*/, 1> &out, const VlUnpacked<QData/*63:0*/, 1> &in) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___trigger_orInto__act_vec_vec\n"); );
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
VL_ATTR_COLD void VBviLiar___024root___dump_triggers__act(const VlUnpacked<QData/*63:0*/, 1> &triggers, const std::string &tag);
#endif  // VL_DEBUG

bool VBviLiar___024root___eval_phase__act(VBviLiar___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___eval_phase__act\n"); );
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    {
        // Inlined CFunc: _eval_triggers_vec__act
        vlSelfRef.__VactTriggered[0U] = (QData)((IData)(
                                                        ((IData)(vlSelfRef.CLK) 
                                                         & (~ (IData)(vlSelfRef.__Vtrigprevexpr___TOP__CLK__1)))));
        vlSelfRef.__Vtrigprevexpr___TOP__CLK__1 = vlSelfRef.CLK;
    }
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VBviLiar___024root___dump_triggers__act(vlSelfRef.__VactTriggered, "act"s);
    }
#endif
    VBviLiar___024root___trigger_orInto__act_vec_vec(vlSelfRef.__VnbaTriggered, vlSelfRef.__VactTriggered);
    return (0U);
}

void VBviLiar___024root___trigger_clear__act(VlUnpacked<QData/*63:0*/, 1> &out) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___trigger_clear__act\n"); );
    // Locals
    IData/*31:0*/ n;
    // Body
    n = 0U;
    do {
        out[n] = 0ULL;
        n = ((IData)(1U) + n);
    } while ((1U > n));
}

bool VBviLiar___024root___eval_phase__nba(VBviLiar___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___eval_phase__nba\n"); );
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*0:0*/ __VnbaExecute;
    // Body
    __VnbaExecute = VBviLiar___024root___trigger_anySet__act(vlSelfRef.__VnbaTriggered);
    if (__VnbaExecute) {
        {
            // Inlined CFunc: _eval_nba
            if ((1ULL & vlSelfRef.__VnbaTriggered[0U])) {
                {
                    // Inlined CFunc: _nba_sequent__TOP__0
                    if (vlSelfRef.RST_N) {
                        if (vlSelfRef.EN_put) {
                            vlSelfRef.BviLiar__DOT__stored 
                                = vlSelfRef.put_x;
                        }
                    } else {
                        vlSelfRef.BviLiar__DOT__stored = 0U;
                    }
                    vlSelfRef.STORED = vlSelfRef.BviLiar__DOT__stored;
                    vlSelfRef.PEEK = ((IData)(vlSelfRef.put_x) 
                                      ^ (IData)(vlSelfRef.BviLiar__DOT__stored));
                }
            }
        }
        VBviLiar___024root___trigger_clear__act(vlSelfRef.__VnbaTriggered);
    }
    return (__VnbaExecute);
}

void VBviLiar___024root___eval(VBviLiar___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___eval\n"); );
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    IData/*31:0*/ __VicoIterCount;
    IData/*31:0*/ __VnbaIterCount;
    // Body
    __VicoIterCount = 0U;
    do {
        if (VL_UNLIKELY(((0x00002710U < __VicoIterCount)))) {
#ifdef VL_DEBUG
            VBviLiar___024root___dump_triggers__ico(vlSelfRef.__VicoTriggered, "ico"s);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviLiar.v", 4, "", "DIDNOTCONVERGE: Input combinational region did not converge after '--converge-limit' of 10000 tries");
        }
        __VicoIterCount = ((IData)(1U) + __VicoIterCount);
        vlSelfRef.__VicoPhaseResult = VBviLiar___024root___eval_phase__ico(vlSelf);
    } while (vlSelfRef.__VicoPhaseResult);
    __VnbaIterCount = 0U;
    do {
        if (VL_UNLIKELY(((0x00002710U < __VnbaIterCount)))) {
#ifdef VL_DEBUG
            VBviLiar___024root___dump_triggers__act(vlSelfRef.__VnbaTriggered, "nba"s);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviLiar.v", 4, "", "DIDNOTCONVERGE: NBA region did not converge after '--converge-limit' of 10000 tries");
        }
        __VnbaIterCount = ((IData)(1U) + __VnbaIterCount);
        vlSelfRef.__VactIterCount = 0U;
        do {
            if (VL_UNLIKELY(((0x00002710U < vlSelfRef.__VactIterCount)))) {
#ifdef VL_DEBUG
                VBviLiar___024root___dump_triggers__act(vlSelfRef.__VactTriggered, "act"s);
#endif
                VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviLiar.v", 4, "", "DIDNOTCONVERGE: Active region did not converge after '--converge-limit' of 10000 tries");
            }
            vlSelfRef.__VactIterCount = ((IData)(1U) 
                                         + vlSelfRef.__VactIterCount);
            vlSelfRef.__VactPhaseResult = VBviLiar___024root___eval_phase__act(vlSelf);
        } while (vlSelfRef.__VactPhaseResult);
        vlSelfRef.__VnbaPhaseResult = VBviLiar___024root___eval_phase__nba(vlSelf);
    } while (vlSelfRef.__VnbaPhaseResult);
}

#ifdef VL_DEBUG
void VBviLiar___024root___eval_debug_assertions(VBviLiar___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___eval_debug_assertions\n"); );
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
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
