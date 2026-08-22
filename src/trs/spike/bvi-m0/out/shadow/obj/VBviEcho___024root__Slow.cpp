// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviEcho.h for the primary calling header

#include "VBviEcho__pch.h"
#include "VBviEcho__Syms.h"
#include "VBviEcho___024root.h"

void VBviEcho___024root___ctor_var_reset(VBviEcho___024root* vlSelf);

VBviEcho___024root::VBviEcho___024root(VBviEcho__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    VBviEcho___024root___ctor_var_reset(this);
}

void VBviEcho___024root::__Vconfigure(bool first) {
    if (false && first) {}  // Prevent unused
}

VBviEcho___024root::~VBviEcho___024root() {
}
