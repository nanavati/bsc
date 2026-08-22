// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviFatal.h for the primary calling header

#include "VBviFatal__pch.h"
#include "VBviFatal__Syms.h"
#include "VBviFatal___024root.h"

void VBviFatal___024root___ctor_var_reset(VBviFatal___024root* vlSelf);

VBviFatal___024root::VBviFatal___024root(VBviFatal__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    VBviFatal___024root___ctor_var_reset(this);
}

void VBviFatal___024root::__Vconfigure(bool first) {
    if (false && first) {}  // Prevent unused
}

VBviFatal___024root::~VBviFatal___024root() {
}
