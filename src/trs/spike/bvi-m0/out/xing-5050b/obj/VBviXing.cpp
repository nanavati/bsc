// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "VBviXing__pch.h"

//============================================================
// Constructors

VBviXing::VBviXing(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new VBviXing__Syms(contextp(), _vcname__, this)}
    , SCLK{vlSymsp->TOP.SCLK}
    , DCLK{vlSymsp->TOP.DCLK}
    , RST_N{vlSymsp->TOP.RST_N}
    , EN_send{vlSymsp->TOP.EN_send}
    , s_din{vlSymsp->TOP.s_din}
    , SREG{vlSymsp->TOP.SREG}
    , DREG{vlSymsp->TOP.DREG}
    , rootp{&(vlSymsp->TOP)}
{
    // Register model with the context
    contextp()->addModel(this);
}

VBviXing::VBviXing(const char* _vcname__)
    : VBviXing(Verilated::threadContextp(), _vcname__)
{
}

//============================================================
// Destructor

VBviXing::~VBviXing() {
    delete vlSymsp;
}

//============================================================
// Evaluation function

#ifdef VL_DEBUG
void VBviXing___024root___eval_debug_assertions(VBviXing___024root* vlSelf);
#endif  // VL_DEBUG
void VBviXing___024root___eval_static(VBviXing___024root* vlSelf);
void VBviXing___024root___eval_initial(VBviXing___024root* vlSelf);
void VBviXing___024root___eval_settle(VBviXing___024root* vlSelf);
void VBviXing___024root___eval(VBviXing___024root* vlSelf);

void VBviXing::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VBviXing::eval_step\n"); );
#ifdef VL_DEBUG
    // Debug assertions
    VBviXing___024root___eval_debug_assertions(&(vlSymsp->TOP));
#endif  // VL_DEBUG
    vlSymsp->__Vm_deleter.deleteAll();
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) {
        VL_DEBUG_IF(VL_DBG_MSGF("+ Initial\n"););
        VBviXing___024root___eval_static(&(vlSymsp->TOP));
        VBviXing___024root___eval_initial(&(vlSymsp->TOP));
        VBviXing___024root___eval_settle(&(vlSymsp->TOP));
        vlSymsp->__Vm_didInit = true;
    }
    VL_DEBUG_IF(VL_DBG_MSGF("+ Eval\n"););
    VBviXing___024root___eval(&(vlSymsp->TOP));
    // Evaluate cleanup
    Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);
}

//============================================================
// Events and timing
bool VBviXing::eventsPending() { return false; }

uint64_t VBviXing::nextTimeSlot() {
    VL_FATAL_MT(__FILE__, __LINE__, "", "No delays in the design");
    return 0;
}

//============================================================
// Utilities

const char* VBviXing::name() const {
    return vlSymsp->name();
}

//============================================================
// Invoke final blocks

void VBviXing___024root___eval_final(VBviXing___024root* vlSelf);

VL_ATTR_COLD void VBviXing::final() {
    contextp()->executingFinal(true);
    VBviXing___024root___eval_final(&(vlSymsp->TOP));
    contextp()->executingFinal(false);
}

//============================================================
// Implementations of abstract methods from VerilatedModel

const char* VBviXing::hierName() const { return vlSymsp->name(); }
const char* VBviXing::modelName() const { return "VBviXing"; }
unsigned VBviXing::threads() const { return 1; }
void VBviXing::prepareClone() const { contextp()->prepareClone(); }
void VBviXing::atClone() const {
    contextp()->threadPoolpOnClone();
}
