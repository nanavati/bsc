// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See VBviViolator.h for the primary calling header

#ifndef VERILATED_VBVIVIOLATOR___024ROOT_H_
#define VERILATED_VBVIVIOLATOR___024ROOT_H_  // guard

#include "verilated.h"


class VBviViolator__Syms;

class alignas(VL_CACHE_LINE_BYTES) VBviViolator___024root final {
  public:

    // DESIGN SPECIFIC STATE
    VL_IN8(CLK,0,0);
    VL_IN8(RST_N,0,0);
    VL_IN8(EN_put,0,0);
    VL_IN8(put_x,7,0);
    VL_OUT8(COUNT,7,0);
    CData/*7:0*/ BviViolator__DOT__cnt;
    CData/*0:0*/ __VstlFirstIteration;
    CData/*0:0*/ __VstlPhaseResult;
    CData/*0:0*/ __Vtrigprevexpr_h5367cfe6__0;
    CData/*0:0*/ __VactPhaseResult;
    CData/*0:0*/ __VnbaPhaseResult;
    IData/*31:0*/ __VactIterCount;
    VlUnpacked<QData/*63:0*/, 1> __VstlTriggered;
    VlUnpacked<QData/*63:0*/, 1> __VactTriggered;
    VlUnpacked<QData/*63:0*/, 1> __VnbaTriggered;

    // INTERNAL VARIABLES
    VBviViolator__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    VBviViolator___024root(VBviViolator__Syms* symsp, const char* namep);
    ~VBviViolator___024root();
    VL_UNCOPYABLE(VBviViolator___024root);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
