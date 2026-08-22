// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviLiar.h for the primary calling header

#include "VBviLiar__pch.h"
#include "VBviLiar___024root.h"

VL_INLINE_OPT void VBviLiar___024root___ico_sequent__TOP__0(VBviLiar___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___ico_sequent__TOP__0\n"); );
    // Body
    vlSelf->PEEK = ((IData)(vlSelf->BviLiar__DOT__stored) 
                    ^ (IData)(vlSelf->put_x));
}

void VBviLiar___024root___eval_ico(VBviLiar___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___eval_ico\n"); );
    // Body
    if ((1ULL & vlSelf->__VicoTriggered.word(0U))) {
        VBviLiar___024root___ico_sequent__TOP__0(vlSelf);
    }
}

void VBviLiar___024root___eval_triggers__ico(VBviLiar___024root* vlSelf);

bool VBviLiar___024root___eval_phase__ico(VBviLiar___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___eval_phase__ico\n"); );
    // Init
    CData/*0:0*/ __VicoExecute;
    // Body
    VBviLiar___024root___eval_triggers__ico(vlSelf);
    __VicoExecute = vlSelf->__VicoTriggered.any();
    if (__VicoExecute) {
        VBviLiar___024root___eval_ico(vlSelf);
    }
    return (__VicoExecute);
}

void VBviLiar___024root___eval_act(VBviLiar___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___eval_act\n"); );
}

VL_INLINE_OPT void VBviLiar___024root___nba_sequent__TOP__0(VBviLiar___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___nba_sequent__TOP__0\n"); );
    // Body
    if (vlSelf->RST_N) {
        if (vlSelf->EN_put) {
            vlSelf->BviLiar__DOT__stored = vlSelf->put_x;
        }
    } else {
        vlSelf->BviLiar__DOT__stored = 0U;
    }
    vlSelf->STORED = vlSelf->BviLiar__DOT__stored;
    vlSelf->PEEK = ((IData)(vlSelf->BviLiar__DOT__stored) 
                    ^ (IData)(vlSelf->put_x));
}

void VBviLiar___024root___eval_nba(VBviLiar___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___eval_nba\n"); );
    // Body
    if ((1ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VBviLiar___024root___nba_sequent__TOP__0(vlSelf);
    }
}

void VBviLiar___024root___eval_triggers__act(VBviLiar___024root* vlSelf);

bool VBviLiar___024root___eval_phase__act(VBviLiar___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___eval_phase__act\n"); );
    // Init
    VlTriggerVec<1> __VpreTriggered;
    CData/*0:0*/ __VactExecute;
    // Body
    VBviLiar___024root___eval_triggers__act(vlSelf);
    __VactExecute = vlSelf->__VactTriggered.any();
    if (__VactExecute) {
        __VpreTriggered.andNot(vlSelf->__VactTriggered, vlSelf->__VnbaTriggered);
        vlSelf->__VnbaTriggered.thisOr(vlSelf->__VactTriggered);
        VBviLiar___024root___eval_act(vlSelf);
    }
    return (__VactExecute);
}

bool VBviLiar___024root___eval_phase__nba(VBviLiar___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___eval_phase__nba\n"); );
    // Init
    CData/*0:0*/ __VnbaExecute;
    // Body
    __VnbaExecute = vlSelf->__VnbaTriggered.any();
    if (__VnbaExecute) {
        VBviLiar___024root___eval_nba(vlSelf);
        vlSelf->__VnbaTriggered.clear();
    }
    return (__VnbaExecute);
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviLiar___024root___dump_triggers__ico(VBviLiar___024root* vlSelf);
#endif  // VL_DEBUG
#ifdef VL_DEBUG
VL_ATTR_COLD void VBviLiar___024root___dump_triggers__nba(VBviLiar___024root* vlSelf);
#endif  // VL_DEBUG
#ifdef VL_DEBUG
VL_ATTR_COLD void VBviLiar___024root___dump_triggers__act(VBviLiar___024root* vlSelf);
#endif  // VL_DEBUG

void VBviLiar___024root___eval(VBviLiar___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___eval\n"); );
    // Init
    IData/*31:0*/ __VicoIterCount;
    CData/*0:0*/ __VicoContinue;
    IData/*31:0*/ __VnbaIterCount;
    CData/*0:0*/ __VnbaContinue;
    // Body
    __VicoIterCount = 0U;
    vlSelf->__VicoFirstIteration = 1U;
    __VicoContinue = 1U;
    while (__VicoContinue) {
        if (VL_UNLIKELY((0x64U < __VicoIterCount))) {
#ifdef VL_DEBUG
            VBviLiar___024root___dump_triggers__ico(vlSelf);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviLiar.v", 4, "", "Input combinational region did not converge.");
        }
        __VicoIterCount = ((IData)(1U) + __VicoIterCount);
        __VicoContinue = 0U;
        if (VBviLiar___024root___eval_phase__ico(vlSelf)) {
            __VicoContinue = 1U;
        }
        vlSelf->__VicoFirstIteration = 0U;
    }
    __VnbaIterCount = 0U;
    __VnbaContinue = 1U;
    while (__VnbaContinue) {
        if (VL_UNLIKELY((0x64U < __VnbaIterCount))) {
#ifdef VL_DEBUG
            VBviLiar___024root___dump_triggers__nba(vlSelf);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviLiar.v", 4, "", "NBA region did not converge.");
        }
        __VnbaIterCount = ((IData)(1U) + __VnbaIterCount);
        __VnbaContinue = 0U;
        vlSelf->__VactIterCount = 0U;
        vlSelf->__VactContinue = 1U;
        while (vlSelf->__VactContinue) {
            if (VL_UNLIKELY((0x64U < vlSelf->__VactIterCount))) {
#ifdef VL_DEBUG
                VBviLiar___024root___dump_triggers__act(vlSelf);
#endif
                VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviLiar.v", 4, "", "Active region did not converge.");
            }
            vlSelf->__VactIterCount = ((IData)(1U) 
                                       + vlSelf->__VactIterCount);
            vlSelf->__VactContinue = 0U;
            if (VBviLiar___024root___eval_phase__act(vlSelf)) {
                vlSelf->__VactContinue = 1U;
            }
        }
        if (VBviLiar___024root___eval_phase__nba(vlSelf)) {
            __VnbaContinue = 1U;
        }
    }
}

#ifdef VL_DEBUG
void VBviLiar___024root___eval_debug_assertions(VBviLiar___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((vlSelf->CLK & 0xfeU))) {
        Verilated::overWidthError("CLK");}
    if (VL_UNLIKELY((vlSelf->RST_N & 0xfeU))) {
        Verilated::overWidthError("RST_N");}
    if (VL_UNLIKELY((vlSelf->EN_put & 0xfeU))) {
        Verilated::overWidthError("EN_put");}
}
#endif  // VL_DEBUG
