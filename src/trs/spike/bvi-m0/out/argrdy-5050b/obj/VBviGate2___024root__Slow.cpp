// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviGate2.h for the primary calling header

#include "VBviGate2__pch.h"

void VBviGate2___024root___ctor_var_reset(VBviGate2___024root* vlSelf);

VBviGate2___024root::VBviGate2___024root(VBviGate2__Syms* symsp, const char* namep)
 {
    vlSymsp = symsp;
    vlNamep = strdup(namep);
    // Reset structure values
    VBviGate2___024root___ctor_var_reset(this);
}

void VBviGate2___024root::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

VBviGate2___024root::~VBviGate2___024root() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
