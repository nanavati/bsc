// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "VBviGate2__pch.h"

//============================================================
// Constructors

VBviGate2::VBviGate2(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new VBviGate2__Syms(contextp(), _vcname__, this)}
    , CLK{vlSymsp->TOP.CLK}
    , RST_N{vlSymsp->TOP.RST_N}
    , EN_put{vlSymsp->TOP.EN_put}
    , put_x{vlSymsp->TOP.put_x}
    , RDY_put{vlSymsp->TOP.RDY_put}
    , STORED{vlSymsp->TOP.STORED}
    , rootp{&(vlSymsp->TOP)}
{
    // Register model with the context
    contextp()->addModel(this);
}

VBviGate2::VBviGate2(const char* _vcname__)
    : VBviGate2(Verilated::threadContextp(), _vcname__)
{
}

//============================================================
// Destructor

VBviGate2::~VBviGate2() {
    delete vlSymsp;
}

//============================================================
// Evaluation function

#ifdef VL_DEBUG
void VBviGate2___024root___eval_debug_assertions(VBviGate2___024root* vlSelf);
#endif  // VL_DEBUG
void VBviGate2___024root___eval_static(VBviGate2___024root* vlSelf);
void VBviGate2___024root___eval_initial(VBviGate2___024root* vlSelf);
void VBviGate2___024root___eval_settle(VBviGate2___024root* vlSelf);
void VBviGate2___024root___eval(VBviGate2___024root* vlSelf);

void VBviGate2::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VBviGate2::eval_step\n"); );
#ifdef VL_DEBUG
    // Debug assertions
    VBviGate2___024root___eval_debug_assertions(&(vlSymsp->TOP));
#endif  // VL_DEBUG
    vlSymsp->__Vm_deleter.deleteAll();
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) {
        vlSymsp->__Vm_didInit = true;
        VL_DEBUG_IF(VL_DBG_MSGF("+ Initial\n"););
        VBviGate2___024root___eval_static(&(vlSymsp->TOP));
        VBviGate2___024root___eval_initial(&(vlSymsp->TOP));
        VBviGate2___024root___eval_settle(&(vlSymsp->TOP));
    }
    VL_DEBUG_IF(VL_DBG_MSGF("+ Eval\n"););
    VBviGate2___024root___eval(&(vlSymsp->TOP));
    // Evaluate cleanup
    Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);
}

//============================================================
// Events and timing
bool VBviGate2::eventsPending() { return false; }

uint64_t VBviGate2::nextTimeSlot() {
    VL_FATAL_MT(__FILE__, __LINE__, "", "%Error: No delays in the design");
    return 0;
}

//============================================================
// Utilities

const char* VBviGate2::name() const {
    return vlSymsp->name();
}

//============================================================
// Invoke final blocks

void VBviGate2___024root___eval_final(VBviGate2___024root* vlSelf);

VL_ATTR_COLD void VBviGate2::final() {
    VBviGate2___024root___eval_final(&(vlSymsp->TOP));
}

//============================================================
// Implementations of abstract methods from VerilatedModel

const char* VBviGate2::hierName() const { return vlSymsp->name(); }
const char* VBviGate2::modelName() const { return "VBviGate2"; }
unsigned VBviGate2::threads() const { return 1; }
void VBviGate2::prepareClone() const { contextp()->prepareClone(); }
void VBviGate2::atClone() const {
    contextp()->threadPoolpOnClone();
}

//============================================================
// Trace configuration

VL_ATTR_COLD void VBviGate2::trace(VerilatedVcdC* tfp, int levels, int options) {
    vl_fatal(__FILE__, __LINE__, __FILE__,"'VBviGate2::trace()' called on model that was Verilated without --trace option");
}
