// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See VBviCounter.h for the primary calling header

#ifndef VERILATED_VBVICOUNTER___024ROOT_H_
#define VERILATED_VBVICOUNTER___024ROOT_H_  // guard

#include "verilated.h"


class VBviCounter__Syms;

class alignas(VL_CACHE_LINE_BYTES) VBviCounter___024root final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    VL_IN8(CLK,0,0);
    VL_IN8(RST_N,0,0);
    VL_IN8(EN_bump,0,0);
    VL_IN8(bump_amt,7,0);
    VL_OUT8(count,7,0);
    VL_OUT8(RDY_bump,0,0);
    CData/*7:0*/ BviCounter__DOT__c;
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
    VBviCounter__Syms* const vlSymsp;

    // CONSTRUCTORS
    VBviCounter___024root(VBviCounter__Syms* symsp, const char* v__name);
    ~VBviCounter___024root();
    VL_UNCOPYABLE(VBviCounter___024root);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
