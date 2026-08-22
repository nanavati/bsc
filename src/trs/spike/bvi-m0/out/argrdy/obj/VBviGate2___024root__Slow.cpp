// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviGate2.h for the primary calling header

#include "VBviGate2__pch.h"
#include "VBviGate2__Syms.h"
#include "VBviGate2___024root.h"

void VBviGate2___024root___ctor_var_reset(VBviGate2___024root* vlSelf);

VBviGate2___024root::VBviGate2___024root(VBviGate2__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    VBviGate2___024root___ctor_var_reset(this);
}

void VBviGate2___024root::__Vconfigure(bool first) {
    if (false && first) {}  // Prevent unused
}

VBviGate2___024root::~VBviGate2___024root() {
}
