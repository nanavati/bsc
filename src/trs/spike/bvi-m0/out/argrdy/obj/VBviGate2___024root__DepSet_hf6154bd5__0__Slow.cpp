// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviGate2.h for the primary calling header

#include "VBviGate2__pch.h"
#include "VBviGate2__Syms.h"
#include "VBviGate2___024root.h"

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviGate2___024root___dump_triggers__stl(VBviGate2___024root* vlSelf);
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviGate2___024root___eval_triggers__stl(VBviGate2___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviGate2__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviGate2___024root___eval_triggers__stl\n"); );
    // Body
    vlSelf->__VstlTriggered.set(0U, (IData)(vlSelf->__VstlFirstIteration));
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VBviGate2___024root___dump_triggers__stl(vlSelf);
    }
#endif
}
