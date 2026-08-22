// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviFatal.h for the primary calling header

#include "VBviFatal__pch.h"

void VBviFatal___024root___ctor_var_reset(VBviFatal___024root* vlSelf);

VBviFatal___024root::VBviFatal___024root(VBviFatal__Syms* symsp, const char* namep)
 {
    vlSymsp = symsp;
    vlNamep = strdup(namep);
    // Reset structure values
    VBviFatal___024root___ctor_var_reset(this);
}

void VBviFatal___024root::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

VBviFatal___024root::~VBviFatal___024root() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
