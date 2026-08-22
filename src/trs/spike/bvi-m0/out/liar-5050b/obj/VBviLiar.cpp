// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "VBviLiar__pch.h"

//============================================================
// Constructors

VBviLiar::VBviLiar(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new VBviLiar__Syms(contextp(), _vcname__, this)}
    , CLK{vlSymsp->TOP.CLK}
    , RST_N{vlSymsp->TOP.RST_N}
    , EN_put{vlSymsp->TOP.EN_put}
    , put_x{vlSymsp->TOP.put_x}
    , PEEK{vlSymsp->TOP.PEEK}
    , STORED{vlSymsp->TOP.STORED}
    , rootp{&(vlSymsp->TOP)}
{
    // Register model with the context
    contextp()->addModel(this);
}

VBviLiar::VBviLiar(const char* _vcname__)
    : VBviLiar(Verilated::threadContextp(), _vcname__)
{
}

//============================================================
// Destructor

VBviLiar::~VBviLiar() {
    delete vlSymsp;
}

//============================================================
// Evaluation function

#ifdef VL_DEBUG
void VBviLiar___024root___eval_debug_assertions(VBviLiar___024root* vlSelf);
#endif  // VL_DEBUG
void VBviLiar___024root___eval_static(VBviLiar___024root* vlSelf);
void VBviLiar___024root___eval_initial(VBviLiar___024root* vlSelf);
void VBviLiar___024root___eval_settle(VBviLiar___024root* vlSelf);
void VBviLiar___024root___eval(VBviLiar___024root* vlSelf);

void VBviLiar::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VBviLiar::eval_step\n"); );
#ifdef VL_DEBUG
    // Debug assertions
    VBviLiar___024root___eval_debug_assertions(&(vlSymsp->TOP));
#endif  // VL_DEBUG
    vlSymsp->__Vm_deleter.deleteAll();
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) {
        VL_DEBUG_IF(VL_DBG_MSGF("+ Initial\n"););
        VBviLiar___024root___eval_static(&(vlSymsp->TOP));
        VBviLiar___024root___eval_initial(&(vlSymsp->TOP));
        VBviLiar___024root___eval_settle(&(vlSymsp->TOP));
        vlSymsp->__Vm_didInit = true;
    }
    VL_DEBUG_IF(VL_DBG_MSGF("+ Eval\n"););
    VBviLiar___024root___eval(&(vlSymsp->TOP));
    // Evaluate cleanup
    Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);
}

//============================================================
// Events and timing
bool VBviLiar::eventsPending() { return false; }

uint64_t VBviLiar::nextTimeSlot() {
    VL_FATAL_MT(__FILE__, __LINE__, "", "No delays in the design");
    return 0;
}

//============================================================
// Utilities

const char* VBviLiar::name() const {
    return vlSymsp->name();
}

//============================================================
// Invoke final blocks

void VBviLiar___024root___eval_final(VBviLiar___024root* vlSelf);

VL_ATTR_COLD void VBviLiar::final() {
    contextp()->executingFinal(true);
    VBviLiar___024root___eval_final(&(vlSymsp->TOP));
    contextp()->executingFinal(false);
}

//============================================================
// Implementations of abstract methods from VerilatedModel

const char* VBviLiar::hierName() const { return vlSymsp->name(); }
const char* VBviLiar::modelName() const { return "VBviLiar"; }
unsigned VBviLiar::threads() const { return 1; }
void VBviLiar::prepareClone() const { contextp()->prepareClone(); }
void VBviLiar::atClone() const {
    contextp()->threadPoolpOnClone();
}
