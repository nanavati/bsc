// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "VBviCounter__pch.h"

//============================================================
// Constructors

VBviCounter::VBviCounter(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new VBviCounter__Syms(contextp(), _vcname__, this)}
    , CLK{vlSymsp->TOP.CLK}
    , RST_N{vlSymsp->TOP.RST_N}
    , EN_bump{vlSymsp->TOP.EN_bump}
    , bump_amt{vlSymsp->TOP.bump_amt}
    , count{vlSymsp->TOP.count}
    , RDY_bump{vlSymsp->TOP.RDY_bump}
    , rootp{&(vlSymsp->TOP)}
{
    // Register model with the context
    contextp()->addModel(this);
}

VBviCounter::VBviCounter(const char* _vcname__)
    : VBviCounter(Verilated::threadContextp(), _vcname__)
{
}

//============================================================
// Destructor

VBviCounter::~VBviCounter() {
    delete vlSymsp;
}

//============================================================
// Evaluation function

#ifdef VL_DEBUG
void VBviCounter___024root___eval_debug_assertions(VBviCounter___024root* vlSelf);
#endif  // VL_DEBUG
void VBviCounter___024root___eval_static(VBviCounter___024root* vlSelf);
void VBviCounter___024root___eval_initial(VBviCounter___024root* vlSelf);
void VBviCounter___024root___eval_settle(VBviCounter___024root* vlSelf);
void VBviCounter___024root___eval(VBviCounter___024root* vlSelf);

void VBviCounter::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VBviCounter::eval_step\n"); );
#ifdef VL_DEBUG
    // Debug assertions
    VBviCounter___024root___eval_debug_assertions(&(vlSymsp->TOP));
#endif  // VL_DEBUG
    vlSymsp->__Vm_deleter.deleteAll();
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) {
        vlSymsp->__Vm_didInit = true;
        VL_DEBUG_IF(VL_DBG_MSGF("+ Initial\n"););
        VBviCounter___024root___eval_static(&(vlSymsp->TOP));
        VBviCounter___024root___eval_initial(&(vlSymsp->TOP));
        VBviCounter___024root___eval_settle(&(vlSymsp->TOP));
    }
    VL_DEBUG_IF(VL_DBG_MSGF("+ Eval\n"););
    VBviCounter___024root___eval(&(vlSymsp->TOP));
    // Evaluate cleanup
    Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);
}

//============================================================
// Events and timing
bool VBviCounter::eventsPending() { return false; }

uint64_t VBviCounter::nextTimeSlot() {
    VL_FATAL_MT(__FILE__, __LINE__, "", "%Error: No delays in the design");
    return 0;
}

//============================================================
// Utilities

const char* VBviCounter::name() const {
    return vlSymsp->name();
}

//============================================================
// Invoke final blocks

void VBviCounter___024root___eval_final(VBviCounter___024root* vlSelf);

VL_ATTR_COLD void VBviCounter::final() {
    VBviCounter___024root___eval_final(&(vlSymsp->TOP));
}

//============================================================
// Implementations of abstract methods from VerilatedModel

const char* VBviCounter::hierName() const { return vlSymsp->name(); }
const char* VBviCounter::modelName() const { return "VBviCounter"; }
unsigned VBviCounter::threads() const { return 1; }
void VBviCounter::prepareClone() const { contextp()->prepareClone(); }
void VBviCounter::atClone() const {
    contextp()->threadPoolpOnClone();
}

//============================================================
// Trace configuration

VL_ATTR_COLD void VBviCounter::trace(VerilatedVcdC* tfp, int levels, int options) {
    vl_fatal(__FILE__, __LINE__, __FILE__,"'VBviCounter::trace()' called on model that was Verilated without --trace option");
}
