// Top-level driver for "verilated" objects (Verilog compiled with verilator)

#include <stdlib.h>

#include <verilated.h>

#ifdef BSV_POSITIVE_RESET
#define BSV_RESET_VALUE 1
#else
#define BSV_RESET_VALUE 0
#endif

#ifndef BSV_RESET_NAME
#define BSV_RESET_NAME RST_N
#endif

#define Q(x) #x
#define QUOTE(x) Q(x)
#define APPEND(x,y) x ## y

#define mkV(name) APPEND(V,name)

#include QUOTE(mkV(TOP).h)

// If "verilator --trace" is used, include the tracing class
#if VM_TRACE
# include <verilated_vcd_c.h>
#endif

// Simulation time is owned by the context and drives $time in Verilog.
// (No sc_time_stamp() here: Verilator supplies a weak default, and
// VerilatedContext::time() falls back to it while time is still zero,
// so defining it in terms of the context would recurse.)
static VerilatedContext* contextp = NULL;

#ifndef BSC_VLT_TIMING

// Model built without --timing: delays inside the Verilog are ignored,
// so the external clock/reset schedule below is the only source of
// events and time can advance in fixed steps.

inline void step (mkV(TOP)* TOP, VerilatedVcdC* tfp, vluint64_t incr)
{
#if VM_TRACE
    if (tfp)
      tfp->dump(contextp->time());
#endif
    TOP->eval ();
    contextp->timeInc(incr);
}

#else // BSC_VLT_TIMING

// Model built with --timing: delays inside the Verilog are honored, so
// the model has its own timed-event queue (e.g. a ClockGen primitive
// generating a waveform by delay).  In addition to driving the external
// clock/reset schedule, the harness must evaluate the model at every
// time slot where internal events mature; otherwise delayed processes
// would never resume.

static VerilatedVcdC* s_tfp = NULL;

// Evaluate the model at the current simulation time and record the
// resulting values in the trace (at most one record per time slot,
// since a slot can be evaluated more than once).
static void eval_now (mkV(TOP)* TOP)
{
    TOP->eval ();
#if VM_TRACE
    static bool dumped = false;
    static vluint64_t last_dump_time = 0;
    if (s_tfp && (!dumped || contextp->time() != last_dump_time)) {
        s_tfp->dump (contextp->time());
        last_dump_time = contextp->time();
        dumped = true;
    }
#endif
}

// Advance simulation time to 'target', evaluating the model at any
// internal time slots reached on the way.  On return, time == target
// (or $finish was executed).
static void advance_to (mkV(TOP)* TOP, vluint64_t target)
{
    while (!contextp->gotFinish ()) {
        vluint64_t next = target;
        if (TOP->eventsPending ()) {
            vluint64_t slot = TOP->nextTimeSlot ();
            if (slot < next) next = slot;
        }
        contextp->time (next);
        if (next >= target) return;
        eval_now (TOP);
    }
}

#endif // BSC_VLT_TIMING

int main (int argc, char **argv, char **env) {
    contextp = new VerilatedContext;
    contextp->commandArgs (argc, argv);    // remember args

    // Use a hierarchical name that matches 'main.v'
    mkV(TOP)* TOP = new mkV(TOP)(contextp, "main");    // create instance of model

    VerilatedVcdC* tfp = NULL;    // pointer for tracing

#if VM_TRACE
    // If verilator was invoked with --trace argument,
    // and if at run time passed the +bscvcd argument, turn on tracing
    const char* flag = contextp->commandArgsPlusMatch("bscvcd");
    if (flag && 0==strcmp(flag, "+bscvcd")) {
        contextp->traceEverOn(true);  // Verilator must compute traced signals
        VL_PRINTF("Enabling waves into dump.vcd...\n");
        tfp = new VerilatedVcdC;
        TOP->trace(tfp, 99);  // Trace 99 levels of hierarchy
        tfp->open("dump.vcd");  // Open the dump file
    }
#endif

#ifndef BSC_VLT_TIMING

    // initial conditions
    TOP->BSV_RESET_NAME = BSV_RESET_VALUE;
    TOP->CLK = 0;
    step(TOP, tfp, 1);

    // First CLK edge to time 1
    TOP->CLK = 1;
    step(TOP, tfp, 1);

    // De-assert RST at time 2
    TOP->BSV_RESET_NAME = 1 - BSV_RESET_VALUE;
    step(TOP, tfp, 3);

    // now resume normal CLK cycle
    // negedge on 5, posedge on 10
    //
    while (! contextp->gotFinish ()) {

	TOP->CLK = 0;
	step(TOP, tfp, 5);
	if (contextp->gotFinish ()) break;

	TOP->CLK = 1;
	step(TOP, tfp, 5);
    }

#else // BSC_VLT_TIMING

    s_tfp = tfp;

    // initial conditions
    //
    // Event-driven simulators see the reset assert at time 0 as an
    // edge (X -> asserted), which triggers the 'always @(RST edge)'
    // blocks in the asynchronous reset primitives.  Two-state
    // Verilator has no X: inputs start at 0, so a negative reset
    // asserted at time 0 produces no edge and those primitives would
    // never see the assertion.  Evaluate once with the reset
    // deasserted, then assert it, so the assertion is an edge here
    // too (both evaluations are at time 0).
    //
    // The cost of that extra evaluation: latches that an event-driven
    // simulator would leave holding X until reset propagates (e.g.
    // the gate latch in the gated-clock primitives) instead capture
    // the design's out-of-reset state, which can pass one extra clock
    // edge into a gated domain at startup.  Setting the environment
    // variable BSC_VLT_NO_RESET_EDGE at run time skips the deasserted
    // evaluation (reset is then never seen as an edge, so designs
    // relying on asynchronous reset assertion at time 0 will not
    // reset).
    TOP->CLK = 0;
    if (!getenv("BSC_VLT_NO_RESET_EDGE")) {
        TOP->BSV_RESET_NAME = 1 - BSV_RESET_VALUE;
        eval_now (TOP);
    }
    TOP->BSV_RESET_NAME = BSV_RESET_VALUE;
    eval_now (TOP);

    // First CLK edge to time 1
    advance_to (TOP, 1);
    if (! contextp->gotFinish ()) {
        TOP->CLK = 1;
        eval_now (TOP);
    }

    // De-assert RST at time 2
    advance_to (TOP, 2);
    if (! contextp->gotFinish ()) {
        TOP->BSV_RESET_NAME = 1 - BSV_RESET_VALUE;
        eval_now (TOP);
    }

    // now resume normal CLK cycle, interleaved with the model's
    // internal events: negedge on 5, posedge on 10 (mod 10)
    //
    vluint64_t t = 5;
    while (! contextp->gotFinish ()) {

	advance_to (TOP, t);
	if (contextp->gotFinish ()) break;
	TOP->CLK = 0;
	eval_now (TOP);

	advance_to (TOP, t + 5);
	if (contextp->gotFinish ()) break;
	TOP->CLK = 1;
	eval_now (TOP);

	t += 10;
    }

#endif // BSC_VLT_TIMING

    TOP->final ();    // Done simulating

    // Close trace if opened
#if VM_TRACE
    if (tfp) { tfp->close(); }
#endif

    delete TOP;
    TOP = NULL;

    delete contextp;
    contextp = NULL;

    exit (0);
}
