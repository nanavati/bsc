// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "VBviFatal__pch.h"

//============================================================
// Constructors

VBviFatal::VBviFatal(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new VBviFatal__Syms(contextp(), _vcname__, this)}
    , CLK{vlSymsp->TOP.CLK}
    , RST_N{vlSymsp->TOP.RST_N}
    , EN_go{vlSymsp->TOP.EN_go}
    , OUT{vlSymsp->TOP.OUT}
    , rootp{&(vlSymsp->TOP)}
{
    // Register model with the context
    contextp()->addModel(this);
}

VBviFatal::VBviFatal(const char* _vcname__)
    : VBviFatal(Verilated::threadContextp(), _vcname__)
{
}

//============================================================
// Destructor

VBviFatal::~VBviFatal() {
    delete vlSymsp;
}

//============================================================
// Evaluation function

#ifdef VL_DEBUG
void VBviFatal___024root___eval_debug_assertions(VBviFatal___024root* vlSelf);
#endif  // VL_DEBUG
void VBviFatal___024root___eval_static(VBviFatal___024root* vlSelf);
void VBviFatal___024root___eval_initial(VBviFatal___024root* vlSelf);
void VBviFatal___024root___eval_settle(VBviFatal___024root* vlSelf);
void VBviFatal___024root___eval(VBviFatal___024root* vlSelf);

void VBviFatal::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VBviFatal::eval_step\n"); );
#ifdef VL_DEBUG
    // Debug assertions
    VBviFatal___024root___eval_debug_assertions(&(vlSymsp->TOP));
#endif  // VL_DEBUG
    vlSymsp->__Vm_deleter.deleteAll();
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) {
        VL_DEBUG_IF(VL_DBG_MSGF("+ Initial\n"););
        VBviFatal___024root___eval_static(&(vlSymsp->TOP));
        VBviFatal___024root___eval_initial(&(vlSymsp->TOP));
        VBviFatal___024root___eval_settle(&(vlSymsp->TOP));
        vlSymsp->__Vm_didInit = true;
    }
    VL_DEBUG_IF(VL_DBG_MSGF("+ Eval\n"););
    VBviFatal___024root___eval(&(vlSymsp->TOP));
    // Evaluate cleanup
    Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);
}

//============================================================
// Events and timing
bool VBviFatal::eventsPending() { return false; }

uint64_t VBviFatal::nextTimeSlot() {
    VL_FATAL_MT(__FILE__, __LINE__, "", "No delays in the design");
    return 0;
}

//============================================================
// Utilities

const char* VBviFatal::name() const {
    return vlSymsp->name();
}

//============================================================
// Invoke final blocks

void VBviFatal___024root___eval_final(VBviFatal___024root* vlSelf);

VL_ATTR_COLD void VBviFatal::final() {
    contextp()->executingFinal(true);
    VBviFatal___024root___eval_final(&(vlSymsp->TOP));
    contextp()->executingFinal(false);
}

//============================================================
// Implementations of abstract methods from VerilatedModel

const char* VBviFatal::hierName() const { return vlSymsp->name(); }
const char* VBviFatal::modelName() const { return "VBviFatal"; }
unsigned VBviFatal::threads() const { return 1; }
void VBviFatal::prepareClone() const { contextp()->prepareClone(); }
void VBviFatal::atClone() const {
    contextp()->threadPoolpOnClone();
}
