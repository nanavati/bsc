// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef VERILATED_VBVIVIOLATOR__SYMS_H_
#define VERILATED_VBVIVIOLATOR__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODEL CLASS

#include "VBviViolator.h"

// INCLUDE MODULE CLASSES
#include "VBviViolator___024root.h"

// SYMS CLASS (contains all model state)
class alignas(VL_CACHE_LINE_BYTES) VBviViolator__Syms final : public VerilatedSyms {
  public:
    // INTERNAL STATE
    VBviViolator* const __Vm_modelp;
    VlDeleter __Vm_deleter;
    bool __Vm_didInit = false;

    // MODULE INSTANCE STATE
    VBviViolator___024root         TOP;

    // CONSTRUCTORS
    VBviViolator__Syms(VerilatedContext* contextp, const char* namep, VBviViolator* modelp);
    ~VBviViolator__Syms();

    // METHODS
    const char* name() const { return TOP.vlNamep; }
};

#endif  // guard
