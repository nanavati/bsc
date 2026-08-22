// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviParams.h for the primary calling header

#include "VBviParams__pch.h"
#include "VBviParams__Syms.h"
#include "VBviParams___024root.h"

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviParams___024root___dump_triggers__act(VBviParams___024root* vlSelf);
#endif  // VL_DEBUG

void VBviParams___024root___eval_triggers__act(VBviParams___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviParams__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviParams___024root___eval_triggers__act\n"); );
    // Body
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VBviParams___024root___dump_triggers__act(vlSelf);
    }
#endif
}
