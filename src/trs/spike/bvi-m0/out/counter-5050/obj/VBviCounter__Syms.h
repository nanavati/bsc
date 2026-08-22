// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef VERILATED_VBVICOUNTER__SYMS_H_
#define VERILATED_VBVICOUNTER__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODEL CLASS

#include "VBviCounter.h"

// INCLUDE MODULE CLASSES
#include "VBviCounter___024root.h"

// SYMS CLASS (contains all model state)
class alignas(VL_CACHE_LINE_BYTES) VBviCounter__Syms final : public VerilatedSyms {
  public:
    // INTERNAL STATE
    VBviCounter* const __Vm_modelp;
    VlDeleter __Vm_deleter;
    bool __Vm_didInit = false;

    // MODULE INSTANCE STATE
    VBviCounter___024root          TOP;

    // CONSTRUCTORS
    VBviCounter__Syms(VerilatedContext* contextp, const char* namep, VBviCounter* modelp);
    ~VBviCounter__Syms();

    // METHODS
    const char* name() const { return TOP.vlNamep; }
};

#endif  // guard
