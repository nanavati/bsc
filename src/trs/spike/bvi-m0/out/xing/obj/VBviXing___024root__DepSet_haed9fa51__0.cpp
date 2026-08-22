// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviXing.h for the primary calling header

#include "VBviXing__pch.h"
#include "VBviXing___024root.h"

void VBviXing___024root___eval_act(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_act\n"); );
}

VL_INLINE_OPT void VBviXing___024root___nba_sequent__TOP__0(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___nba_sequent__TOP__0\n"); );
    // Body
    vlSelf->BviXing__DOT__dreg = ((IData)(vlSelf->RST_N)
                                   ? (IData)(vlSelf->BviXing__DOT__sreg)
                                   : 0U);
    vlSelf->DREG = vlSelf->BviXing__DOT__dreg;
}

VL_INLINE_OPT void VBviXing___024root___nba_sequent__TOP__1(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___nba_sequent__TOP__1\n"); );
    // Body
    if (vlSelf->RST_N) {
        if (vlSelf->EN_send) {
            vlSelf->BviXing__DOT__sreg = vlSelf->s_din;
        }
    } else {
        vlSelf->BviXing__DOT__sreg = 0U;
    }
    vlSelf->SREG = vlSelf->BviXing__DOT__sreg;
}

void VBviXing___024root___eval_nba(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_nba\n"); );
    // Body
    if ((2ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VBviXing___024root___nba_sequent__TOP__0(vlSelf);
    }
    if ((1ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VBviXing___024root___nba_sequent__TOP__1(vlSelf);
    }
}

void VBviXing___024root___eval_triggers__act(VBviXing___024root* vlSelf);

bool VBviXing___024root___eval_phase__act(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_phase__act\n"); );
    // Init
    VlTriggerVec<2> __VpreTriggered;
    CData/*0:0*/ __VactExecute;
    // Body
    VBviXing___024root___eval_triggers__act(vlSelf);
    __VactExecute = vlSelf->__VactTriggered.any();
    if (__VactExecute) {
        __VpreTriggered.andNot(vlSelf->__VactTriggered, vlSelf->__VnbaTriggered);
        vlSelf->__VnbaTriggered.thisOr(vlSelf->__VactTriggered);
        VBviXing___024root___eval_act(vlSelf);
    }
    return (__VactExecute);
}

bool VBviXing___024root___eval_phase__nba(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_phase__nba\n"); );
    // Init
    CData/*0:0*/ __VnbaExecute;
    // Body
    __VnbaExecute = vlSelf->__VnbaTriggered.any();
    if (__VnbaExecute) {
        VBviXing___024root___eval_nba(vlSelf);
        vlSelf->__VnbaTriggered.clear();
    }
    return (__VnbaExecute);
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviXing___024root___dump_triggers__nba(VBviXing___024root* vlSelf);
#endif  // VL_DEBUG
#ifdef VL_DEBUG
VL_ATTR_COLD void VBviXing___024root___dump_triggers__act(VBviXing___024root* vlSelf);
#endif  // VL_DEBUG

void VBviXing___024root___eval(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval\n"); );
    // Init
    IData/*31:0*/ __VnbaIterCount;
    CData/*0:0*/ __VnbaContinue;
    // Body
    __VnbaIterCount = 0U;
    __VnbaContinue = 1U;
    while (__VnbaContinue) {
        if (VL_UNLIKELY((0x64U < __VnbaIterCount))) {
#ifdef VL_DEBUG
            VBviXing___024root___dump_triggers__nba(vlSelf);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviXing.v", 3, "", "NBA region did not converge.");
        }
        __VnbaIterCount = ((IData)(1U) + __VnbaIterCount);
        __VnbaContinue = 0U;
        vlSelf->__VactIterCount = 0U;
        vlSelf->__VactContinue = 1U;
        while (vlSelf->__VactContinue) {
            if (VL_UNLIKELY((0x64U < vlSelf->__VactIterCount))) {
#ifdef VL_DEBUG
                VBviXing___024root___dump_triggers__act(vlSelf);
#endif
                VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviXing.v", 3, "", "Active region did not converge.");
            }
            vlSelf->__VactIterCount = ((IData)(1U) 
                                       + vlSelf->__VactIterCount);
            vlSelf->__VactContinue = 0U;
            if (VBviXing___024root___eval_phase__act(vlSelf)) {
                vlSelf->__VactContinue = 1U;
            }
        }
        if (VBviXing___024root___eval_phase__nba(vlSelf)) {
            __VnbaContinue = 1U;
        }
    }
}

#ifdef VL_DEBUG
void VBviXing___024root___eval_debug_assertions(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((vlSelf->SCLK & 0xfeU))) {
        Verilated::overWidthError("SCLK");}
    if (VL_UNLIKELY((vlSelf->DCLK & 0xfeU))) {
        Verilated::overWidthError("DCLK");}
    if (VL_UNLIKELY((vlSelf->RST_N & 0xfeU))) {
        Verilated::overWidthError("RST_N");}
    if (VL_UNLIKELY((vlSelf->EN_send & 0xfeU))) {
        Verilated::overWidthError("EN_send");}
}
#endif  // VL_DEBUG
