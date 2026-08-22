// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviParams.h for the primary calling header

#include "VBviParams__pch.h"

void VBviParams___024root___eval(VBviParams___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___eval\n"); );
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

#ifdef VL_DEBUG
void VBviParams___024root___eval_debug_assertions(VBviParams___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___eval_debug_assertions\n"); );
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    if (VL_UNLIKELY(((vlSelfRef.CLK & 0xfeU)))) {
        Verilated::overWidthError("CLK");
    }
}
#endif  // VL_DEBUG
