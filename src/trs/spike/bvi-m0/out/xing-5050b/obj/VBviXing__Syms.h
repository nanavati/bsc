// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef VERILATED_VBVIXING__SYMS_H_
#define VERILATED_VBVIXING__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODEL CLASS

#include "VBviXing.h"

// INCLUDE MODULE CLASSES
#include "VBviXing___024root.h"

// SYMS CLASS (contains all model state)
class alignas(VL_CACHE_LINE_BYTES) VBviXing__Syms final : public VerilatedSyms {
  public:
    // INTERNAL STATE
    VBviXing* const __Vm_modelp;
    VlDeleter __Vm_deleter;
    bool __Vm_didInit = false;

    // MODULE INSTANCE STATE
    VBviXing___024root             TOP;

    // CONSTRUCTORS
    VBviXing__Syms(VerilatedContext* contextp, const char* namep, VBviXing* modelp);
    ~VBviXing__Syms();

    // METHODS
    const char* name() const { return TOP.vlNamep; }
};

#endif  // guard
