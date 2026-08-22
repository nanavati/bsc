// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef VERILATED_VBVILIAR__SYMS_H_
#define VERILATED_VBVILIAR__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODEL CLASS

#include "VBviLiar.h"

// INCLUDE MODULE CLASSES
#include "VBviLiar___024root.h"

// SYMS CLASS (contains all model state)
class alignas(VL_CACHE_LINE_BYTES) VBviLiar__Syms final : public VerilatedSyms {
  public:
    // INTERNAL STATE
    VBviLiar* const __Vm_modelp;
    VlDeleter __Vm_deleter;
    bool __Vm_didInit = false;

    // MODULE INSTANCE STATE
    VBviLiar___024root             TOP;

    // CONSTRUCTORS
    VBviLiar__Syms(VerilatedContext* contextp, const char* namep, VBviLiar* modelp);
    ~VBviLiar__Syms();

    // METHODS
    const char* name() const { return TOP.vlNamep; }
};

#endif  // guard
