// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviParams.h for the primary calling header

#include "VBviParams__pch.h"

void VBviParams___024root___ctor_var_reset(VBviParams___024root* vlSelf);

VBviParams___024root::VBviParams___024root(VBviParams__Syms* symsp, const char* namep)
 {
    vlSymsp = symsp;
    vlNamep = strdup(namep);
    // Reset structure values
    VBviParams___024root___ctor_var_reset(this);
}

void VBviParams___024root::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

VBviParams___024root::~VBviParams___024root() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
