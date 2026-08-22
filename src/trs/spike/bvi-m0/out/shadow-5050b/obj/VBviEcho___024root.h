// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See VBviEcho.h for the primary calling header

#ifndef VERILATED_VBVIECHO___024ROOT_H_
#define VERILATED_VBVIECHO___024ROOT_H_  // guard

#include "verilated.h"


class VBviEcho__Syms;

class alignas(VL_CACHE_LINE_BYTES) VBviEcho___024root final {
  public:

    // DESIGN SPECIFIC STATE
    VL_IN8(CLK,0,0);
    VL_IN8(RST_N,0,0);
    VL_IN8(EN,0,0);
    VL_IN8(IN,7,0);
    VL_OUT8(OUT,7,0);
    VL_OUT8(LAST,7,0);
    CData/*7:0*/ BviEcho__DOT__last;
    CData/*0:0*/ __VstlFirstIteration;
    CData/*0:0*/ __VstlPhaseResult;
    CData/*0:0*/ __Vtrigprevexpr___TOP__CLK__0;
    CData/*0:0*/ __Vtrigprevexpr___TOP__RST_N__0;
    CData/*0:0*/ __Vtrigprevexpr___TOP__EN__0;
    CData/*7:0*/ __Vtrigprevexpr___TOP__IN__0;
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
    VBviEcho__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    VBviEcho___024root(VBviEcho__Syms* symsp, const char* namep);
    ~VBviEcho___024root();
    VL_UNCOPYABLE(VBviEcho___024root);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
