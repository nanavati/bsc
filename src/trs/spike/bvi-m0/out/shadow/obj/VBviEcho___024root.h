// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See VBviEcho.h for the primary calling header

#ifndef VERILATED_VBVIECHO___024ROOT_H_
#define VERILATED_VBVIECHO___024ROOT_H_  // guard

#include "verilated.h"


class VBviEcho__Syms;

class alignas(VL_CACHE_LINE_BYTES) VBviEcho___024root final : public VerilatedModule {
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
    CData/*0:0*/ __VicoFirstIteration;
    CData/*0:0*/ __Vtrigprevexpr___TOP__CLK__0;
    CData/*0:0*/ __VactContinue;
    IData/*31:0*/ __VactIterCount;
    VlTriggerVec<1> __VstlTriggered;
    VlTriggerVec<1> __VicoTriggered;
    VlTriggerVec<1> __VactTriggered;
    VlTriggerVec<1> __VnbaTriggered;

    // INTERNAL VARIABLES
    VBviEcho__Syms* const vlSymsp;

    // CONSTRUCTORS
    VBviEcho___024root(VBviEcho__Syms* symsp, const char* v__name);
    ~VBviEcho___024root();
    VL_UNCOPYABLE(VBviEcho___024root);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
