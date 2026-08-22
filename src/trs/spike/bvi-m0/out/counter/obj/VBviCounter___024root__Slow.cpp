// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviCounter.h for the primary calling header

#include "VBviCounter__pch.h"
#include "VBviCounter__Syms.h"
#include "VBviCounter___024root.h"

void VBviCounter___024root___ctor_var_reset(VBviCounter___024root* vlSelf);

VBviCounter___024root::VBviCounter___024root(VBviCounter__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    VBviCounter___024root___ctor_var_reset(this);
}

void VBviCounter___024root::__Vconfigure(bool first) {
    if (false && first) {}  // Prevent unused
}

VBviCounter___024root::~VBviCounter___024root() {
}
