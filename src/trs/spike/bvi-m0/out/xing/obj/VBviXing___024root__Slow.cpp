// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviXing.h for the primary calling header

#include "VBviXing__pch.h"
#include "VBviXing__Syms.h"
#include "VBviXing___024root.h"

void VBviXing___024root___ctor_var_reset(VBviXing___024root* vlSelf);

VBviXing___024root::VBviXing___024root(VBviXing__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    VBviXing___024root___ctor_var_reset(this);
}

void VBviXing___024root::__Vconfigure(bool first) {
    if (false && first) {}  // Prevent unused
}

VBviXing___024root::~VBviXing___024root() {
}
