// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviFatal.h for the primary calling header

#include "VBviFatal__pch.h"
#include "VBviFatal___024root.h"

void VBviFatal___024root___eval_act(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval_act\n"); );
}

void VBviFatal___024root___nba_sequent__TOP__0(VBviFatal___024root* vlSelf);

void VBviFatal___024root___eval_nba(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval_nba\n"); );
    // Body
    if ((1ULL & vlSelf->__VnbaTriggered.word(0U))) {
        VBviFatal___024root___nba_sequent__TOP__0(vlSelf);
    }
}

void VBviFatal___024root___eval_triggers__act(VBviFatal___024root* vlSelf);

bool VBviFatal___024root___eval_phase__act(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval_phase__act\n"); );
    // Init
    VlTriggerVec<1> __VpreTriggered;
    CData/*0:0*/ __VactExecute;
    // Body
    VBviFatal___024root___eval_triggers__act(vlSelf);
    __VactExecute = vlSelf->__VactTriggered.any();
    if (__VactExecute) {
        __VpreTriggered.andNot(vlSelf->__VactTriggered, vlSelf->__VnbaTriggered);
        vlSelf->__VnbaTriggered.thisOr(vlSelf->__VactTriggered);
        VBviFatal___024root___eval_act(vlSelf);
    }
    return (__VactExecute);
}

bool VBviFatal___024root___eval_phase__nba(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval_phase__nba\n"); );
    // Init
    CData/*0:0*/ __VnbaExecute;
    // Body
    __VnbaExecute = vlSelf->__VnbaTriggered.any();
    if (__VnbaExecute) {
        VBviFatal___024root___eval_nba(vlSelf);
        vlSelf->__VnbaTriggered.clear();
    }
    return (__VnbaExecute);
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviFatal___024root___dump_triggers__nba(VBviFatal___024root* vlSelf);
#endif  // VL_DEBUG
#ifdef VL_DEBUG
VL_ATTR_COLD void VBviFatal___024root___dump_triggers__act(VBviFatal___024root* vlSelf);
#endif  // VL_DEBUG

void VBviFatal___024root___eval(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval\n"); );
    // Init
    IData/*31:0*/ __VnbaIterCount;
    CData/*0:0*/ __VnbaContinue;
    // Body
    __VnbaIterCount = 0U;
    __VnbaContinue = 1U;
    while (__VnbaContinue) {
        if (VL_UNLIKELY((0x64U < __VnbaIterCount))) {
#ifdef VL_DEBUG
            VBviFatal___024root___dump_triggers__nba(vlSelf);
#endif
            VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviFatal.v", 4, "", "NBA region did not converge.");
        }
        __VnbaIterCount = ((IData)(1U) + __VnbaIterCount);
        __VnbaContinue = 0U;
        vlSelf->__VactIterCount = 0U;
        vlSelf->__VactContinue = 1U;
        while (vlSelf->__VactContinue) {
            if (VL_UNLIKELY((0x64U < vlSelf->__VactIterCount))) {
#ifdef VL_DEBUG
                VBviFatal___024root___dump_triggers__act(vlSelf);
#endif
                VL_FATAL_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviFatal.v", 4, "", "Active region did not converge.");
            }
            vlSelf->__VactIterCount = ((IData)(1U) 
                                       + vlSelf->__VactIterCount);
            vlSelf->__VactContinue = 0U;
            if (VBviFatal___024root___eval_phase__act(vlSelf)) {
                vlSelf->__VactContinue = 1U;
            }
        }
        if (VBviFatal___024root___eval_phase__nba(vlSelf)) {
            __VnbaContinue = 1U;
        }
    }
}

#ifdef VL_DEBUG
void VBviFatal___024root___eval_debug_assertions(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((vlSelf->CLK & 0xfeU))) {
        Verilated::overWidthError("CLK");}
    if (VL_UNLIKELY((vlSelf->RST_N & 0xfeU))) {
        Verilated::overWidthError("RST_N");}
    if (VL_UNLIKELY((vlSelf->EN_go & 0xfeU))) {
        Verilated::overWidthError("EN_go");}
}
#endif  // VL_DEBUG
