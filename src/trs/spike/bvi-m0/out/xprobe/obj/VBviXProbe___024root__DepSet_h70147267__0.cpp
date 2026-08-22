// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviXProbe.h for the primary calling header

#include "VBviXProbe__pch.h"
#include "VBviXProbe__Syms.h"
#include "VBviXProbe___024root.h"

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviXProbe___024root___dump_triggers__act(VBviXProbe___024root* vlSelf);
#endif  // VL_DEBUG

void VBviXProbe___024root___eval_triggers__act(VBviXProbe___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviXProbe__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviXProbe___024root___eval_triggers__act\n"); );
    // Body
    vlSelf->__VactTriggered.set(0U, ((IData)(vlSelf->CLK) 
                                     & (~ (IData)(vlSelf->__Vtrigprevexpr___TOP__CLK__0))));
    vlSelf->__Vtrigprevexpr___TOP__CLK__0 = vlSelf->CLK;
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VBviXProbe___024root___dump_triggers__act(vlSelf);
    }
#endif
}
