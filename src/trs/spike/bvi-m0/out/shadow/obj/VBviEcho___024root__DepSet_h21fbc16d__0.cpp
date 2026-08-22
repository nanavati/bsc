// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviEcho.h for the primary calling header

#include "VBviEcho__pch.h"
#include "VBviEcho___024root.h"

VL_INLINE_OPT void VBviEcho___024root___ico_sequent__TOP__0(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___ico_sequent__TOP__0\n"); );
    // Body
    vlSelf->OUT = (0xffU & ((IData)(1U) + (IData)(vlSelf->IN)));
}

void VBviEcho___024root___eval_ico(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___eval_ico\n"); );
    // Body
    if ((1ULL & vlSelf->__VicoTriggered.word(0U))) {
        VBviEcho___024root___ico_sequent__TOP__0(vlSelf);
    }
}

void VBviEcho___024root___eval_triggers__ico(VBviEcho___024root* vlSelf);

bool VBviEcho___024root___eval_phase__ico(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___eval_phase__ico\n"); );
    // Init
    CData/*0:0*/ __VicoExecute;
    // Body
    VBviEcho___024root___eval_triggers__ico(vlSelf);
    __VicoExecute = vlSelf->__VicoTriggered.any();
    if (__VicoExecute) {
        VBviEcho___024root___eval_ico(vlSelf);
    }
    return (__VicoExecute);
}

void VBviEcho___024root___eval_act(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___eval_act\n"); );
}

VL_INLINE_OPT void VBviEcho___024root___nba_sequent__TOP__0(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___nba_sequent__TOP__0\n"); );
    // Body
    if (vlSelf->RST_N) {
        if (vlSelf->EN) {
            vlSelf->BviEcho__DOT__last = vlSelf->IN;
        }
    } else {
        vlSelf->BviEcho__DOT__last = 0U;
    }
    vlSelf->LAST = vlSelf->BviEcho__DOT__last;
}

void VBviEcho___024root___eval_nba(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___eval_nba\n"); );
    // Body
    if ((1ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VBviEcho___024root___nba_sequent__TOP__0(vlSelf);
    }
}

void VBviEcho___024root___eval_triggers__act(VBviEcho___024root* vlSelf);

bool VBviEcho___024root___eval_phase__act(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___eval_phase__act\n"); );
    // Init
    VlTriggerVec<1> __VpreTriggered;
    CData/*0:0*/ __VactExecute;
    // Body
    VBviEcho___024root___eval_triggers__act(vlSelf);
    __VactExecute = vlSelf->__VactTriggered.any();
    if (__VactExecute) {
        __VpreTriggered.andNot(vlSelf->__VactTriggered, vlSelf->__VnbaTriggered);
        vlSelf->__VnbaTriggered.thisOr(vlSelf->__VactTriggered);
        VBviEcho___024root___eval_act(vlSelf);
    }
    return (__VactExecute);
}

bool VBviEcho___024root___eval_phase__nba(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___eval_phase__nba\n"); );
    // Init
    CData/*0:0*/ __VnbaExecute;
    // Body
    __VnbaExecute = vlSelf->__VnbaTriggered.any();
    if (__VnbaExecute) {
        VBviEcho___024root___eval_nba(vlSelf);
        vlSelf->__VnbaTriggered.clear();
    }
    return (__VnbaExecute);
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviEcho___024root___dump_triggers__ico(VBviEcho___024root* vlSelf);
#endif  // VL_DEBUG
#ifdef VL_DEBUG
VL_ATTR_COLD void VBviEcho___024root___dump_triggers__nba(VBviEcho___024root* vlSelf);
#endif  // VL_DEBUG
#ifdef VL_DEBUG
VL_ATTR_COLD void VBviEcho___024root___dump_triggers__act(VBviEcho___024root* vlSelf);
#endif  // VL_DEBUG

void VBviEcho___024root___eval(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___eval\n"); );
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
            VBviEcho___024root___dump_triggers__ico(vlSelf);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviEcho.v", 4, "", "Input combinational region did not converge.");
        }
        __VicoIterCount = ((IData)(1U) + __VicoIterCount);
        __VicoContinue = 0U;
        if (VBviEcho___024root___eval_phase__ico(vlSelf)) {
            __VicoContinue = 1U;
        }
        vlSelf->__VicoFirstIteration = 0U;
    }
    __VnbaIterCount = 0U;
    __VnbaContinue = 1U;
    while (__VnbaContinue) {
        if (VL_UNLIKELY((0x64U < __VnbaIterCount))) {
#ifdef VL_DEBUG
            VBviEcho___024root___dump_triggers__nba(vlSelf);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviEcho.v", 4, "", "NBA region did not converge.");
        }
        __VnbaIterCount = ((IData)(1U) + __VnbaIterCount);
        __VnbaContinue = 0U;
        vlSelf->__VactIterCount = 0U;
        vlSelf->__VactContinue = 1U;
        while (vlSelf->__VactContinue) {
            if (VL_UNLIKELY((0x64U < vlSelf->__VactIterCount))) {
#ifdef VL_DEBUG
                VBviEcho___024root___dump_triggers__act(vlSelf);
#endif
                VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviEcho.v", 4, "", "Active region did not converge.");
            }
            vlSelf->__VactIterCount = ((IData)(1U) 
                                       + vlSelf->__VactIterCount);
            vlSelf->__VactContinue = 0U;
            if (VBviEcho___024root___eval_phase__act(vlSelf)) {
                vlSelf->__VactContinue = 1U;
            }
        }
        if (VBviEcho___024root___eval_phase__nba(vlSelf)) {
            __VnbaContinue = 1U;
        }
    }
}

#ifdef VL_DEBUG
void VBviEcho___024root___eval_debug_assertions(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((vlSelf->CLK & 0xfeU))) {
        Verilated::overWidthError("CLK");}
    if (VL_UNLIKELY((vlSelf->RST_N & 0xfeU))) {
        Verilated::overWidthError("RST_N");}
    if (VL_UNLIKELY((vlSelf->EN & 0xfeU))) {
        Verilated::overWidthError("EN");}
}
#endif  // VL_DEBUG
