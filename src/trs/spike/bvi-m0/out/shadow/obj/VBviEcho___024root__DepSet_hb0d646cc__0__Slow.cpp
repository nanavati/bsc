// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviEcho.h for the primary calling header

#include "VBviEcho__pch.h"
#include "VBviEcho__Syms.h"
#include "VBviEcho___024root.h"

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviEcho___024root___dump_triggers__stl(VBviEcho___024root* vlSelf);
#endif  // VL_DEBUG

VL_ATTR_COLD void VBviEcho___024root___eval_triggers__stl(VBviEcho___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviEcho__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviEcho___024root___eval_triggers__stl\n"); );
    // Body
    vlSelf->__VstlTriggered.set(0U, (IData)(vlSelf->__VstlFirstIteration));
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VBviEcho___024root___dump_triggers__stl(vlSelf);
    }
#endif
}
