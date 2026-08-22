// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviFatal.h for the primary calling header

#include "VBviFatal__pch.h"
#include "VBviFatal__Syms.h"
#include "VBviFatal___024root.h"

#ifdef VL_DEBUG
VL_ATTR_COLD void VBviFatal___024root___dump_triggers__act(VBviFatal___024root* vlSelf);
#endif  // VL_DEBUG

void VBviFatal___024root___eval_triggers__act(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___eval_triggers__act\n"); );
    // Body
    vlSelf->__VactTriggered.set(0U, ((IData)(vlSelf->CLK) 
                                     & (~ (IData)(vlSelf->__Vtrigprevexpr___TOP__CLK__0))));
    vlSelf->__Vtrigprevexpr___TOP__CLK__0 = vlSelf->CLK;
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        VBviFatal___024root___dump_triggers__act(vlSelf);
    }
#endif
}

VL_INLINE_OPT void VBviFatal___024root___nba_sequent__TOP__0(VBviFatal___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    VBviFatal__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    VBviFatal___024root___nba_sequent__TOP__0\n"); );
    // Body
    if (((IData)(vlSelf->RST_N) & (IData)(vlSelf->EN_go))) {
        if (vlSymsp->_vm_contextp__->assertOn()) {
            if (VL_UNLIKELY(vlSymsp->_vm_contextp__->assertOn())) {
                VL_WRITEF("[%0t] %%Fatal: BviFatal.v:10: Assertion failed in %NBviFatal: fixture fatal fired\n",
                          64,VL_TIME_UNITED_Q(1),-12,
                          vlSymsp->name());
                VL_STOP_MT("/home/user/bsc-matx/src/trs/spike/bvi-m0/rtl/BviFatal.v", 10, "");
            }
        }
    }
}
