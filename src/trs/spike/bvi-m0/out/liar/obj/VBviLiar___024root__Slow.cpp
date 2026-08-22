// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviLiar.h for the primary calling header

#include "VBviLiar__pch.h"
#include "VBviLiar__Syms.h"
#include "VBviLiar___024root.h"

void VBviLiar___024root___ctor_var_reset(VBviLiar___024root* vlSelf);

VBviLiar___024root::VBviLiar___024root(VBviLiar__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    VBviLiar___024root___ctor_var_reset(this);
}

void VBviLiar___024root::__Vconfigure(bool first) {
    if (false && first) {}  // Prevent unused
}

VBviLiar___024root::~VBviLiar___024root() {
}
