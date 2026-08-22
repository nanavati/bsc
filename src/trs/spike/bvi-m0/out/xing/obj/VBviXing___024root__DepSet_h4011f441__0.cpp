// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviXing.h for the primary calling header

#include "VBviXing__pch.h"
#include "VBviXing__Syms.h"
#include "VBviXing___024root.h"

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviXing___024root___dump_triggers__act(VBviXing___024root* vlSelf);
#endif  // VL_DEBUG

void VBviXing___024root___eval_triggers__act(VBviXing___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXing__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXing___024root___eval_triggers__act\n"); );
    // Body
    vlSelf->__VactTriggered.set(0U, ((IData)(vlSelf->SCLK) 
                                     & (~ (IData)(vlSelf->__Vtrigprevexpr___TOP__SCLK__0))));
    vlSelf->__VactTriggered.set(1U, ((IData)(vlSelf->DCLK) 
                                     & (~ (IData)(vlSelf->__Vtrigprevexpr___TOP__DCLK__0))));
    vlSelf->__Vtrigprevexpr___TOP__SCLK__0 = vlSelf->SCLK;
    vlSelf->__Vtrigprevexpr___TOP__DCLK__0 = vlSelf->DCLK;
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VBviXing___024root___dump_triggers__act(vlSelf);
    }
#endif
}
