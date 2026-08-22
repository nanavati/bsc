// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef VERILATED_VBVIECHO__SYMS_H_
#define VERILATED_VBVIECHO__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODEL CLASS

#include "VBviEcho.h"

// INCLUDE MODULE CLASSES
#include "VBviEcho___024root.h"

// SYMS CLASS (contains all model state)
class alignas(VL_CACHE_LINE_BYTES) VBviEcho__Syms final : public VerilatedSyms {
  public:
    // INTERNAL STATE
    VBviEcho* const __Vm_modelp;
    VlDeleter __Vm_deleter;
    bool __Vm_didInit = false;

    // MODULE INSTANCE STATE
    VBviEcho___024root             TOP;

    // CONSTRUCTORS
    VBviEcho__Syms(VerilatedContext* contextp, const char* namep, VBviEcho* modelp);
    ~VBviEcho__Syms();

    // METHODS
    const char* name() const { return TOP.vlNamep; }
};

#endif  // guard
