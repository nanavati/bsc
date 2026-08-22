// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See VBviXing.h for the primary calling header

#ifndef VERILATED_VBVIXING___024ROOT_H_
#define VERILATED_VBVIXING___024ROOT_H_  // guard

#include "verilated.h"


class VBviXing__Syms;

class alignas(VL_CACHE_LINE_BYTES) VBviXing___024root final {
  public:

    // DESIGN SPECIFIC STATE
    VL_IN8(SCLK,0,0);
    VL_IN8(DCLK,0,0);
    VL_IN8(RST_N,0,0);
    VL_IN8(EN_send,0,0);
    VL_IN8(s_din,7,0);
    VL_OUT8(SREG,7,0);
    VL_OUT8(DREG,7,0);
    CData/*7:0*/ BviXing__DOT__sreg;
    CData/*7:0*/ BviXing__DOT__dreg;
    CData/*0:0*/ __VstlFirstIteration;
    CData/*0:0*/ __VstlPhaseResult;
    CData/*0:0*/ __Vtrigprevexpr___TOP__SCLK__0;
    CData/*0:0*/ __Vtrigprevexpr___TOP__DCLK__0;
    CData/*0:0*/ __VactPhaseResult;
    CData/*0:0*/ __VnbaPhaseResult;
    IData/*31:0*/ __VactIterCount;
    VlUnpacked<QData/*63:0*/, 1> __VstlTriggered;
    VlUnpacked<QData/*63:0*/, 1> __VactTriggered;
    VlUnpacked<QData/*63:0*/, 1> __VnbaTriggered;

    // INTERNAL VARIABLES
    VBviXing__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    VBviXing___024root(VBviXing__Syms* symsp, const char* namep);
    ~VBviXing___024root();
    VL_UNCOPYABLE(VBviXing___024root);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
