// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviViolator.h for the primary calling header

#include "VBviViolator__pch.h"

void VBviViolator___024root___ctor_var_reset(VBviViolator___024root* vlSelf);

VBviViolator___024root::VBviViolator___024root(VBviViolator__Syms* symsp, const char* namep)
 {
    vlSymsp = symsp;
    vlNamep = strdup(namep);
    // Reset structure values
    VBviViolator___024root___ctor_var_reset(this);
}

void VBviViolator___024root::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

VBviViolator___024root::~VBviViolator___024root() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
