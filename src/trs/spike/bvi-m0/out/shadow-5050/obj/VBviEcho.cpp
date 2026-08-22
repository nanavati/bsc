// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "VBviEcho__pch.h"

//============================================================
// Constructors

VBviEcho::VBviEcho(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new VBviEcho__Syms(contextp(), _vcname__, this)}
    , CLK{vlSymsp->TOP.CLK}
    , RST_N{vlSymsp->TOP.RST_N}
    , EN{vlSymsp->TOP.EN}
    , IN{vlSymsp->TOP.IN}
    , OUT{vlSymsp->TOP.OUT}
    , LAST{vlSymsp->TOP.LAST}
    , rootp{&(vlSymsp->TOP)}
{
    // Register model with the context
    contextp()->addModel(this);
}

VBviEcho::VBviEcho(const char* _vcname__)
    : VBviEcho(Verilated::threadContextp(), _vcname__)
{
}

//============================================================
// Destructor

VBviEcho::~VBviEcho() {
    delete vlSymsp;
}

//============================================================
// Evaluation function

#ifdef VL_DEBUG
void VBviEcho___024root___eval_debug_assertions(VBviEcho___024root* vlSelf);
#endif  // VL_DEBUG
void VBviEcho___024root___eval_static(VBviEcho___024root* vlSelf);
void VBviEcho___024root___eval_initial(VBviEcho___024root* vlSelf);
void VBviEcho___024root___eval_settle(VBviEcho___024root* vlSelf);
void VBviEcho___024root___eval(VBviEcho___024root* vlSelf);

void VBviEcho::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VBviEcho::eval_step\n"); );
#ifdef VL_DEBUG
    // Debug assertions
    VBviEcho___024root___eval_debug_assertions(&(vlSymsp->TOP));
#endif  // VL_DEBUG
    vlSymsp->__Vm_deleter.deleteAll();
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) {
        VL_DEBUG_IF(VL_DBG_MSGF("+ Initial\n"););
        VBviEcho___024root___eval_static(&(vlSymsp->TOP));
        VBviEcho___024root___eval_initial(&(vlSymsp->TOP));
        VBviEcho___024root___eval_settle(&(vlSymsp->TOP));
        vlSymsp->__Vm_didInit = true;
    }
    VL_DEBUG_IF(VL_DBG_MSGF("+ Eval\n"););
    VBviEcho___024root___eval(&(vlSymsp->TOP));
    // Evaluate cleanup
    Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);
}

//============================================================
// Events and timing
bool VBviEcho::eventsPending() { return false; }

uint64_t VBviEcho::nextTimeSlot() {
    VL_FATAL_MT(__FILE__, __LINE__, "", "No delays in the design");
    return 0;
}

//============================================================
// Utilities

const char* VBviEcho::name() const {
    return vlSymsp->name();
}

//============================================================
// Invoke final blocks

void VBviEcho___024root___eval_final(VBviEcho___024root* vlSelf);

VL_ATTR_COLD void VBviEcho::final() {
    contextp()->executingFinal(true);
    VBviEcho___024root___eval_final(&(vlSymsp->TOP));
    contextp()->executingFinal(false);
}

//============================================================
// Implementations of abstract methods from VerilatedModel

const char* VBviEcho::hierName() const { return vlSymsp->name(); }
const char* VBviEcho::modelName() const { return "VBviEcho"; }
unsigned VBviEcho::threads() const { return 1; }
void VBviEcho::prepareClone() const { contextp()->prepareClone(); }
void VBviEcho::atClone() const {
    contextp()->threadPoolpOnClone();
}
