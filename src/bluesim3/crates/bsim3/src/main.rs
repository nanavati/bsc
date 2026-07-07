//! bsim3 — the Bluesim 3 driver.
//!
//! Invoked by `bsc` where `simLink` runs today, or directly by build
//! systems.  Planned subcommands (DESIGN.md §3, §10):
//!
//!   bsim3 ir dump <mod.bir>       pretty-print BIR (P0 diff-testing)
//!   bsim3 link <top> <bir...>     plan + codegen + link a simulation
//!   bsim3 run <top> [args]        JIT-and-run without artifacts

use std::process::ExitCode;

fn usage() -> ExitCode {
    eprintln!("bsim3 {} (phase P0 scaffold)", env!("CARGO_PKG_VERSION"));
    eprintln!("usage: bsim3 ir dump <module.bir>");
    ExitCode::from(2)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        ["ir", "dump", path] => match std::fs::read(path) {
            Ok(bytes) => match bsim3_ir::Design::decode(&bytes) {
                Ok(design) => {
                    println!("{design:#?}");
                    ExitCode::SUCCESS
                }
                Err(e) => {
                    eprintln!("bsim3: {path}: {e}");
                    ExitCode::FAILURE
                }
            },
            Err(e) => {
                eprintln!("bsim3: {path}: {e}");
                ExitCode::FAILURE
            }
        },
        _ => usage(),
    }
}
