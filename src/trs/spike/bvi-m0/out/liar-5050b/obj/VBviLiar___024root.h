// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See VBviLiar.h for the primary calling header

#ifndef VERILATED_VBVILIAR___024ROOT_H_
#define VERILATED_VBVILIAR___024ROOT_H_  // guard

#include "verilated.h"


class VBviLiar__Syms;

class alignas(VL_CACHE_LINE_BYTES) VBviLiar___024root final {
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
    CData/*0:0*/ __VstlPhaseResult;
    CData/*0:0*/ __Vtrigprevexpr___TOP__CLK__0;
    CData/*0:0*/ __Vtrigprevexpr___TOP__RST_N__0;
    CData/*0:0*/ __Vtrigprevexpr___TOP__EN_put__0;
    CData/*7:0*/ __Vtrigprevexpr___TOP__put_x__0;
    CData/*0:0*/ __VicoDidInit;
    CData/*0:0*/ __VicoPhaseResult;
    CData/*0:0*/ __Vtrigprevexpr___TOP__CLK__1;
    CData/*0:0*/ __VactPhaseResult;
    CData/*0:0*/ __VnbaPhaseResult;
    IData/*31:0*/ __VactIterCount;
    VlUnpacked<QData/*63:0*/, 1> __VstlTriggered;
    VlUnpacked<QData/*63:0*/, 2> __VicoTriggered;
    VlUnpacked<QData/*63:0*/, 1> __VactTriggered;
    VlUnpacked<QData/*63:0*/, 1> __VnbaTriggered;

    // INTERNAL VARIABLES
    VBviLiar__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    VBviLiar___024root(VBviLiar__Syms* symsp, const char* namep);
    ~VBviLiar___024root();
    VL_UNCOPYABLE(VBviLiar___024root);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
