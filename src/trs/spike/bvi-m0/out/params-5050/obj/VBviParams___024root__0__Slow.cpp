// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviParams.h for the primary calling header

#include "VBviParams__pch.h"

VL_ATTR_COLD void VBviParams___024root___eval_static(VBviParams___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___eval_static\n"); );
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

VL_ATTR_COLD void VBviParams___024root___eval_initial(VBviParams___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___eval_initial\n"); );
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    {
        // Inlined CFunc: _eval_initial__TOP
        vlSelfRef.P_SINT = 0xfffffffbU;
        vlSelfRef.P_WIDE[0U] = 0x01234567U;
        vlSelfRef.P_WIDE[1U] = 0x89abcdefU;
        vlSelfRef.P_WIDE[2U] = 0x01234567U;
        VL_WRITEF_NX("STR=hello RVAL=2.5\n",0);
    }
}

VL_ATTR_COLD void VBviParams___024root___eval_final(VBviParams___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___eval_final\n"); );
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

VL_ATTR_COLD void VBviParams___024root___eval_settle(VBviParams___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___eval_settle\n"); );
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}

VL_ATTR_COLD void VBviParams___024root___ctor_var_reset(VBviParams___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___ctor_var_reset\n"); );
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelf->CLK = 0;
    vlSelf->P_SINT = 0;
    VL_ZERO_RESET_W(96, vlSelf->P_WIDE);
}
