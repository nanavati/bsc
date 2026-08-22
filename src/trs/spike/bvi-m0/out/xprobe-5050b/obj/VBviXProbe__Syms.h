// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef VERILATED_VBVIXPROBE__SYMS_H_
#define VERILATED_VBVIXPROBE__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODEL CLASS

#include "VBviXProbe.h"

// INCLUDE MODULE CLASSES
#include "VBviXProbe___024root.h"

// SYMS CLASS (contains all model state)
class alignas(VL_CACHE_LINE_BYTES) VBviXProbe__Syms final : public VerilatedSyms {
  public:
    // INTERNAL STATE
    VBviXProbe* const __Vm_modelp;
    VlDeleter __Vm_deleter;
    bool __Vm_didInit = false;

    // MODULE INSTANCE STATE
    VBviXProbe___024root           TOP;

    // CONSTRUCTORS
    VBviXProbe__Syms(VerilatedContext* contextp, const char* namep, VBviXProbe* modelp);
    ~VBviXProbe__Syms();

    // METHODS
    const char* name() const { return TOP.vlNamep; }
};

#endif  // guard
