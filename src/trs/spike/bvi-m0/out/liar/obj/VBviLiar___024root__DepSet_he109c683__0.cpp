// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviLiar.h for the primary calling header

#include "VBviLiar__pch.h"
#include "VBviLiar__Syms.h"
#include "VBviLiar___024root.h"

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviLiar___024root___dump_triggers__ico(VBviLiar___024root* vlSelf);
#endif  // VL_DEBUG

void VBviLiar___024root___eval_triggers__ico(VBviLiar___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___eval_triggers__ico\n"); );
    // Body
    vlSelf->__VicoTriggered.set(0U, (IData)(vlSelf->__VicoFirstIteration));
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VBviLiar___024root___dump_triggers__ico(vlSelf);
    }
#endif
}

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviLiar___024root___dump_triggers__act(VBviLiar___024root* vlSelf);
#endif  // VL_DEBUG

void VBviLiar___024root___eval_triggers__act(VBviLiar___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviLiar__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviLiar___024root___eval_triggers__act\n"); );
    // Body
    vlSelf->__VactTriggered.set(0U, ((IData)(vlSelf->CLK) 
                                     & (~ (IData)(vlSelf->__Vtrigprevexpr___TOP__CLK__0))));
    vlSelf->__Vtrigprevexpr___TOP__CLK__0 = vlSelf->CLK;
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VBviLiar___024root___dump_triggers__act(vlSelf);
    }
#endif
}
