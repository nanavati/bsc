// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See VBviLiar.h for the primary calling header

#ifndef VERILATED_VBVILIAR___024ROOT_H_
#define VERILATED_VBVILIAR___024ROOT_H_  // guard

#include "verilated.h"


class VBviLiar__Syms;

class alignas(VL_CACHE_LINE_BYTES) VBviLiar___024root final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    VL_IN8(CLK,0,0);
    VL_IN8(RST_N,0,0);
    VL_IN8(EN_put,0,0);
    VL_IN8(put_x,7,0);
    VL_OUT8(PEEK,7,0);
    VL_OUT8(STORED,7,0);
    CData/*7:0*/ BviLiar__DOT__stored;
    CData/*0:0*/ __VstlFirstIteration;
    CData/*0:0*/ __VicoFirstIteration;
    CData/*0:0*/ __Vtrigprevexpr___TOP__CLK__0;
    CData/*0:0*/ __VactContinue;
    IData/*31:0*/ __VactIterCount;
    VlTriggerVec<1> __VstlTriggered;
    VlTriggerVec<1> __VicoTriggered;
    VlTriggerVec<1> __VactTriggered;
    VlTriggerVec<1> __VnbaTriggered;

    // INTERNAL VARIABLES
    VBviLiar__Syms* const vlSymsp;

    // CONSTRUCTORS
    VBviLiar___024root(VBviLiar__Syms* symsp, const char* v__name);
    ~VBviLiar___024root();
    VL_UNCOPYABLE(VBviLiar___024root);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
