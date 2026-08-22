// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviXProbe.h for the primary calling header

#include "VBviXProbe__pch.h"
#include "VBviXProbe__Syms.h"
#include "VBviXProbe___024root.h"

void VBviXProbe___024root___ctor_var_reset(VBviXProbe___024root* vlSelf);

VBviXProbe___024root::VBviXProbe___024root(VBviXProbe__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    VBviXProbe___024root___ctor_var_reset(this);
}

void VBviXProbe___024root::__Vconfigure(bool first) {
    if (false && first) {}  // Prevent unused
}

VBviXProbe___024root::~VBviXProbe___024root() {
}
