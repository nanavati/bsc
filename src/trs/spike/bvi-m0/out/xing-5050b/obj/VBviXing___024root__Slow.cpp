// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviXing.h for the primary calling header

#include "VBviXing__pch.h"

void VBviXing___024root___ctor_var_reset(VBviXing___024root* vlSelf);

VBviXing___024root::VBviXing___024root(VBviXing__Syms* symsp, const char* namep)
 {
    vlSymsp = symsp;
    vlNamep = strdup(namep);
    // Reset structure values
    VBviXing___024root___ctor_var_reset(this);
}

void VBviXing___024root::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

VBviXing___024root::~VBviXing___024root() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
