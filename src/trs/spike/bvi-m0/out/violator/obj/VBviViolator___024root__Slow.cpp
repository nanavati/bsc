// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviViolator.h for the primary calling header

#include "VBviViolator__pch.h"
#include "VBviViolator__Syms.h"
#include "VBviViolator___024root.h"

void VBviViolator___024root___ctor_var_reset(VBviViolator___024root* vlSelf);

VBviViolator___024root::VBviViolator___024root(VBviViolator__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    VBviViolator___024root___ctor_var_reset(this);
}

void VBviViolator___024root::__Vconfigure(bool first) {
    if (false && first) {}  // Prevent unused
}

VBviViolator___024root::~VBviViolator___024root() {
}
