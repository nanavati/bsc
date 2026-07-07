# Bluesim 3

A Rust/LLVM simulation backend for BSC — a modern replacement for the
C++-generating Bluesim backend.  See [DESIGN.md](DESIGN.md) for the full
architecture, rationale, and phasing.

Status: **design + scaffolding** (phase P0 of DESIGN.md §10).

## Layout

| Crate | Purpose |
|---|---|
| `bsim3-ir` | BIR (Bluesim IR) schema, loader, verifier — the contract with bsc |
| `bsim3-kernel` | Simulation kernel: event queue, priorities, clocks, resets |
| `bsim3-rt` | Runtime primitives (FIFO, RegFile, …), system tasks |
| `bsim3-wave` | Waveform capture; VCD and FST writers |
| `bsim3-codegen` | LLVM lowering (feature `llvm`; needs `llvm-18-dev`, `libzstd-dev`) |
| `bsim3` | CLI: link planner, JIT/AOT driver, native runner |

## Building

```sh
cargo build            # everything except codegen (no LLVM required)
cargo test
cargo build -p bsim3-codegen --features llvm   # requires llvm-18-dev + libzstd-dev
```
