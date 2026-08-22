// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviEcho.h for the primary calling header

#include "VBviEcho__pch.h"

void VBviEcho___024root___ctor_var_reset(VBviEcho___024root* vlSelf);

VBviEcho___024root::VBviEcho___024root(VBviEcho__Syms* symsp, const char* namep)
 {
    vlSymsp = symsp;
    vlNamep = strdup(namep);
    // Reset structure values
    VBviEcho___024root___ctor_var_reset(this);
}

void VBviEcho___024root::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

VBviEcho___024root::~VBviEcho___024root() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
