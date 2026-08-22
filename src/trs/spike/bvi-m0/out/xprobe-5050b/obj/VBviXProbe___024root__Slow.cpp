// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VBviXProbe.h for the primary calling header

#include "VBviXProbe__pch.h"

void VBviXProbe___024root___ctor_var_reset(VBviXProbe___024root* vlSelf);

VBviXProbe___024root::VBviXProbe___024root(VBviXProbe__Syms* symsp, const char* namep)
 {
    vlSymsp = symsp;
    vlNamep = strdup(namep);
    // Reset structure values
    VBviXProbe___024root___ctor_var_reset(this);
}

void VBviXProbe___024root::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

VBviXProbe___024root::~VBviXProbe___024root() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
