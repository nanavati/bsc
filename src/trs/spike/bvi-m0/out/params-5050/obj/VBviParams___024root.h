// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See VBviParams.h for the primary calling header

#ifndef VERILATED_VBVIPARAMS___024ROOT_H_
#define VERILATED_VBVIPARAMS___024ROOT_H_  // guard

#include "verilated.h"


class VBviParams__Syms;

class alignas(VL_CACHE_LINE_BYTES) VBviParams___024root final {
  public:

    // DESIGN SPECIFIC STATE
    VL_IN8(CLK,0,0);
    VL_OUT(P_SINT,31,0);
    VL_OUTW(P_WIDE,95,0,3);

    // INTERNAL VARIABLES
    VBviParams__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    VBviParams___024root(VBviParams__Syms* symsp, const char* namep);
    ~VBviParams___024root();
    VL_UNCOPYABLE(VBviParams___024root);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
