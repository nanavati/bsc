// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviParams.h for the primary calling header

#include "VBviParams__pch.h"
#include "VBviParams__Syms.h"
#include "VBviParams___024root.h"

void VBviParams___024root___ctor_var_reset(VBviParams___024root* vlSelf);

VBviParams___024root::VBviParams___024root(VBviParams__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    VBviParams___024root___ctor_var_reset(this);
}

void VBviParams___024root::__Vconfigure(bool first) {
    if (false && first) {}  // Prevent unused
}

VBviParams___024root::~VBviParams___024root() {
}
