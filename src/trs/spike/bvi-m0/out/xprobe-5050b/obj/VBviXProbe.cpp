// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "VBviXProbe__pch.h"

//============================================================
// Constructors

VBviXProbe::VBviXProbe(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new VBviXProbe__Syms(contextp(), _vcname__, this)}
    , CLK{vlSymsp->TOP.CLK}
    , RST_N{vlSymsp->TOP.RST_N}
    , RDYX{vlSymsp->TOP.RDYX}
    , Q{vlSymsp->TOP.Q}
    , rootp{&(vlSymsp->TOP)}
{
    // Register model with the context
    contextp()->addModel(this);
}

VBviXProbe::VBviXProbe(const char* _vcname__)
    : VBviXProbe(Verilated::threadContextp(), _vcname__)
{
}

//============================================================
// Destructor

VBviXProbe::~VBviXProbe() {
    delete vlSymsp;
}

//============================================================
// Evaluation function

#ifdef VL_DEBUG
void VBviXProbe___024root___eval_debug_assertions(VBviXProbe___024root* vlSelf);
#endif  // VL_DEBUG
void VBviXProbe___024root___eval_static(VBviXProbe___024root* vlSelf);
void VBviXProbe___024root___eval_initial(VBviXProbe___024root* vlSelf);
void VBviXProbe___024root___eval_settle(VBviXProbe___024root* vlSelf);
void VBviXProbe___024root___eval(VBviXProbe___024root* vlSelf);

void VBviXProbe::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VBviXProbe::eval_step\n"); );
#ifdef VL_DEBUG
    // Debug assertions
    VBviXProbe___024root___eval_debug_assertions(&(vlSymsp->TOP));
#endif  // VL_DEBUG
    vlSymsp->__Vm_deleter.deleteAll();
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) {
        VL_DEBUG_IF(VL_DBG_MSGF("+ Initial\n"););
        VBviXProbe___024root___eval_static(&(vlSymsp->TOP));
        VBviXProbe___024root___eval_initial(&(vlSymsp->TOP));
        VBviXProbe___024root___eval_settle(&(vlSymsp->TOP));
        vlSymsp->__Vm_didInit = true;
    }
    VL_DEBUG_IF(VL_DBG_MSGF("+ Eval\n"););
    VBviXProbe___024root___eval(&(vlSymsp->TOP));
    // Evaluate cleanup
    Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);
}

//============================================================
// Events and timing
bool VBviXProbe::eventsPending() { return false; }

uint64_t VBviXProbe::nextTimeSlot() {
    VL_FATAL_MT(__FILE__, __LINE__, "", "No delays in the design");
    return 0;
}

//============================================================
// Utilities

const char* VBviXProbe::name() const {
    return vlSymsp->name();
}

//============================================================
// Invoke final blocks

void VBviXProbe___024root___eval_final(VBviXProbe___024root* vlSelf);

VL_ATTR_COLD void VBviXProbe::final() {
    contextp()->executingFinal(true);
    VBviXProbe___024root___eval_final(&(vlSymsp->TOP));
    contextp()->executingFinal(false);
}

//============================================================
// Implementations of abstract methods from VerilatedModel

const char* VBviXProbe::hierName() const { return vlSymsp->name(); }
const char* VBviXProbe::modelName() const { return "VBviXProbe"; }
unsigned VBviXProbe::threads() const { return 1; }
void VBviXProbe::prepareClone() const { contextp()->prepareClone(); }
void VBviXProbe::atClone() const {
    contextp()->threadPoolpOnClone();
}
