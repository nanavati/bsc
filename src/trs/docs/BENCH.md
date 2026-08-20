# Three-simulator benchmark — Bluesim vs Verilator vs trs

`tools/bench.py`. Two axes per design:

- **build**: bsc frontend (elaboration) + backend-specific build —
  Bluesim's C++ codegen + g++, Verilator's `--cc --build`, trs's
  `.bir` export + `trs link`.  The testsuite corpus is already an
  excellent COMPILE benchmark (conflict_free_large: 417s Bluesim
  build vs ~18s trs link at last measure); runtime needs the designs
  below.
- **run**: wall time to natural `$finish` (median of `--runs`), peak
  RSS, and cycles/s where the design's cycle count is known.

## Fairness ground rules

- Every leg runs SINGLE-THREADED.
- Verilator runs with NO timing flags (per Ravi: `--timing` has known
  issues, and `--no-timing` would silently ignore stray delays).
  Instead: `BSV_ASSIGNMENT_DELAY` is \`define'd away, bsc's literal
  `#0;` system-task ordering guards are stripped (inert under the C++
  driver — the negedge instant is a plain eval long after posedge
  NBAs settle), and a generic C++ driver toggles CLK/RST_N on the bsc
  top, so all three legs simulate the same closed testbench module.
  Anything else timing-shaped errors loudly for explicit handling.
- Designs terminate themselves (`$finish`): identical workload per
  leg, no `-m` games.
- Cross-leg stdout is byte-compared (Verilator's own `$finish`
  trailer normalized away).  `$random` designs are exempt on the
  Verilator leg only — Verilator's RNG is not glibc's, so the operand
  stream legitimately differs; Bluesim and trs must still match.
- Numbers from an uncalibrated or shared box are INDICATIVE.  The
  authoritative fence runs on the calibrated machine.

## In-repo pool (from sweep telemetry: per-cycle weight + distinct stress characters)

| design | character |
|---|---|
| Long | raw edge/rule dispatch floor (300M posedges, one rule) |
| ConflictFreeLarge | huge rule count per cycle (scheduler-bound) |
| DFT64 v1/v5 | FP dataflow pipeline, FIFO-heavy |
| FloatTest | FP arithmetic battery, wide values |
| TrafficBRAM | BRAM + MIMO buffering, memory-port bound |
| BRAM0Test | BRAM variants battery, wide state |
| Sudoku | deep combinational cones, backtracking search |
| Dividers | iterative arithmetic + $random operands |
| SparseRF | RegFile range traffic |
| Mesa | app-scale packet pipeline |

## External macro pool (clones under the session scratchpad, integration staged)

- **Flute** (bluespec/Flute, RV32/64 5-stage) and **Toooba**
  (bluespec/Toooba, RiscyOO superscalar OOO) — per Ravi, Piccolo is
  NOT worth a third slot: it is Flute's 3-stage sibling from the same
  lineage with a near-identical simulation profile (byte-identical
  Include_bluesim.mk); keep it only as a fallback if Flute fights the
  build.  Both share one recipe: `bsc -u -elab -sim` →
  `bsc -sim -e mkTop_HW_Side` + C_Imported_Functions.c → `Mem.hex` +
  `symbol_table.txt` in CWD (elf_to_hex, needs libelf) →
  `./exe +v1 +tohost` → PASS/FAIL + `$finish`.  In-repo workloads are
  the RISC-V ISA ELFs (short — fine for correctness and BUILD
  benchmarking; Toooba's elaboration is a compile benchmark all by
  itself).  Meaningful core RUNTIME numbers need a Dhrystone/CoreMark
  hex — not shipped in-repo; build via a riscv-gnu toolchain or fetch
  prebuilt when integrating.  Toooba additionally needs its BlueStuff
  submodule (network).
- **BlueLight** (kammoh/bluelight, LWC crypto: Ascon/Xoodyak/GIFT-COFB/
  Gimli/Subterranean) — compute-dense and modern-bsc-friendly, but it
  has NO Bluesim testbench (cocotb/Verilog only) and its `lwc` top is
  not `Empty`, so it needs a small closed BSV TB wrapper (drive
  LwcIfc with in-BSV vectors, self-check, `$finish`) before it can
  enter the pool.  Staged as follow-up.
- BlueCheck / CHERI variants / further candidates: web survey in
  progress; add here as they qualify.

## Running

    BSC=.../bsc TRS=.../trs python3 tools/bench.py \
        [--filter substr] [--runs 3] [--legs bluesim,verilator,trs]

Emits a table per design and `bench-results.json`.  Run only on an
otherwise-idle machine.
