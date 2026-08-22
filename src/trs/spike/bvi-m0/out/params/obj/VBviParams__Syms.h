// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef VERILATED_VBVIPARAMS__SYMS_H_
#define VERILATED_VBVIPARAMS__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODEL CLASS

#include "VBviParams.h"

// INCLUDE MODULE CLASSES
#include "VBviParams___024root.h"

// SYMS CLASS (contains all model state)
class alignas(VL_CACHE_LINE_BYTES)VBviParams__Syms final : public VerilatedSyms {
  public:
    // INTERNAL STATE
    VBviParams* const __Vm_modelp;
    VlDeleter __Vm_deleter;
    bool __Vm_didInit = false;

    // MODULE INSTANCE STATE
    VBviParams___024root           TOP;

    // CONSTRUCTORS
    VBviParams__Syms(VerilatedContext* contextp, const char* namep, VBviParams* modelp);
    ~VBviParams__Syms();

    // METHODS
    const char* name() { return TOP.name(); }
};

#endif  // guard
