// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviLiar.h for the primary calling header

#include "VBviLiar__pch.h"

void VBviLiar___024root___ctor_var_reset(VBviLiar___024root* vlSelf);

VBviLiar___024root::VBviLiar___024root(VBviLiar__Syms* symsp, const char* namep)
 {
    vlSymsp = symsp;
    vlNamep = strdup(namep);
    // Reset structure values
    VBviLiar___024root___ctor_var_reset(this);
}

void VBviLiar___024root::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

VBviLiar___024root::~VBviLiar___024root() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
