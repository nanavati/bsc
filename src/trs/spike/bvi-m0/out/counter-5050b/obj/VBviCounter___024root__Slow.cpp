// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviCounter.h for the primary calling header

#include "VBviCounter__pch.h"

void VBviCounter___024root___ctor_var_reset(VBviCounter___024root* vlSelf);

VBviCounter___024root::VBviCounter___024root(VBviCounter__Syms* symsp, const char* namep)
 {
    vlSymsp = symsp;
    vlNamep = strdup(namep);
    // Reset structure values
    VBviCounter___024root___ctor_var_reset(this);
}

void VBviCounter___024root::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

VBviCounter___024root::~VBviCounter___024root() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
