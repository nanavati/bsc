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
    eprintln!("       bsim3 link <module.bir> [-o <out.cexe>]");
    eprintln!("       bsim3 run <module.bir> [-m max_cycles] [--code <model.so>]");
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
        // bsim3 link: compile the design ahead of time and write the
        // persistent artifact: <out> (wrapper script with the same CLI
        // as reference Bluesim), <out>.bir, <out>.so.  Runs never
        // compile again — same amortization as Verilator/VCS/Bluesim.
        ["link", path, rest @ ..] => {
            let mut out: Option<String> = None;
            let mut interactive = false;
            let mut it = rest.iter();
            while let Some(a) = it.next() {
                match *a {
                    "-o" => out = it.next().map(|s| s.to_string()),
                    "--interactive" => interactive = true,
                    other => {
                        eprintln!("Error: invalid link option '{other}'");
                        return ExitCode::from(2);
                    }
                }
            }
            let base = out.unwrap_or_else(|| {
                format!("{}.cexe", path.strip_suffix(".bir").unwrap_or(path))
            });
            let mut interp = match bsim3_interp::load_file(path, &[], None) {
                Ok(i) => i,
                Err(e) => {
                    eprintln!("bsim3: {e}");
                    return ExitCode::FAILURE;
                }
            };
            if interactive {
                // DEBUG/interactive product: a bluetcl-loadable model
                // .so (docs/TCL-CAPI.md) + the reference's bluesim.tcl
                // wrapper — a different artifact from the fast one
                return link_interactive(path, &base, interp.top_name());
            }
            interp.aot_request_emit(format!("{base}.so").into());
            interp.prime();
            // ineligible designs still get a valid artifact — it runs
            // interpreted (reference Bluesim always yields an
            // executable); only infrastructure failures fail the link
            let compiled = match interp.aot_take_emit_result() {
                Some(bsim3_interp::AotEmit::Compiled) => true,
                Some(bsim3_interp::AotEmit::Failed(e)) => {
                    eprintln!("bsim3 link: {e}");
                    return ExitCode::FAILURE;
                }
                Some(bsim3_interp::AotEmit::Ineligible(e)) => {
                    eprintln!(
                        "bsim3 link: note: compiled mode unavailable ({e}); \
                         artifact will run interpreted"
                    );
                    false
                }
                None => {
                    eprintln!(
                        "bsim3 link: note: compiled mode unavailable \
                         (BSIM3_JIT_TRACE=1 shows why); artifact will run \
                         interpreted"
                    );
                    false
                }
            };
            // .bir sibling: the script runs <base>.bir next to the .so
            let bir_dst = format!("{base}.bir");
            if std::path::Path::new(path).canonicalize().ok()
                != std::path::Path::new(&bir_dst).canonicalize().ok()
            {
                if let Err(e) = std::fs::copy(path, &bir_dst) {
                    eprintln!("bsim3 link: copy {path} -> {bir_dst}: {e}");
                    return ExitCode::FAILURE;
                }
            }
            // user BDPI code travels with the artifact: load_file looks
            // for <base>.bdpi.so next to the (renamed) .bir
            let bdpi_src =
                format!("{}.bdpi.so", path.strip_suffix(".bir").unwrap_or(path));
            let bdpi_dst = format!("{base}.bdpi.so");
            if std::path::Path::new(&bdpi_src).exists()
                && std::path::Path::new(&bdpi_src).canonicalize().ok()
                    != std::path::Path::new(&bdpi_dst).canonicalize().ok()
            {
                if let Err(e) = std::fs::copy(&bdpi_src, &bdpi_dst) {
                    eprintln!("bsim3 link: copy {bdpi_src} -> {bdpi_dst}: {e}");
                    return ExitCode::FAILURE;
                }
            }
            // wrapper script (bsim3 must be on PATH, like bluetcl for
            // reference Bluesim executables)
            let split = std::env::var("BSIM3_JIT_SPLIT").unwrap_or_default();
            let split_arg = if split.is_empty() {
                String::new()
            } else {
                format!(" --split {split}")
            };
            // honor $BSIM3 like bsc's interp wrapper (the testsuite
            // points it at a specific build); the DEFAULT is the
            // absolute path of the binary that linked the artifact —
            // a bare `bsim3` PATH lookup silently picked up stale
            // installs (caught by the perf fence: every artifact ran
            // interpreted under an old inst/bin binary)
            let self_exe = std::env::current_exe()
                .ok()
                .and_then(|p| p.to_str().map(String::from))
                .unwrap_or_else(|| "bsim3".into());
            let script = if compiled {
                format!(
                    "#!/bin/sh\nd=`dirname \"$0\"`\nb=`basename \"$0\"`\n\
                     exec \"${{BSIM3:-{self_exe}}}\" run \"$d/$b.bir\" --code \"$d/$b.so\"{split_arg} ${{1+\"$@\"}}\n"
                )
            } else {
                format!(
                    "#!/bin/sh\nd=`dirname \"$0\"`\nb=`basename \"$0\"`\n\
                     exec \"${{BSIM3:-{self_exe}}}\" run \"$d/$b.bir\" ${{1+\"$@\"}}\n"
                )
            };
            if let Err(e) = std::fs::write(&base, script) {
                eprintln!("bsim3 link: {base}: {e}");
                return ExitCode::FAILURE;
            }
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let _ = std::fs::set_permissions(
                    &base,
                    std::fs::Permissions::from_mode(0o755),
                );
            }
            ExitCode::SUCCESS
        }
        ["run", path, rest @ ..] => {
            // mirror the bluesim.tcl driver's argument handling: -m N is
            // the cycle limit, +foo registers a plusarg (sans '+'),
            // anything else is an error
            let mut max_cycles = u64::MAX;
            let mut plusargs: Vec<String> = Vec::new();
            let mut vcd_file: Option<String> = None;
            let mut code_so: Option<String> = None;
            let mut script_cmds = String::new();
            // bluesim.tcl's usage text, printed for -h and after the
            // deprecated-flag notices; the driver exits 0 in both cases
            let script = path
                .strip_suffix(".bir")
                .unwrap_or(path)
                .to_string();
            let usage_exit = || -> ExitCode {
                println!("Usage: {script} [opts]");
                println!();
                println!("Options:");
                println!("  -c <commands> = execute commands given as an argument");
                println!("  -f <file>     = execute script from file");
                println!("  -h            = print help and exit");
                println!("  -m <N>        = execute for N cycles");
                println!("  -v            = print version information and exit");
                println!("  -V [<file>]   = dump waveforms to VCD file (default: dump.vcd)");
                println!("  +<arg>        = Verilog-style plus-arg");
                println!();
                println!("Examples:");
                println!("  {script}");
                println!("  {script} -m 3000");
                println!("  {script} -V sim.vcd");
                println!("  {script} +doFoo");
                ExitCode::SUCCESS
            };
            let mut it = rest.iter().peekable();
            while let Some(a) = it.next() {
                match *a {
                    // deprecated interactive-debug flags: notice + usage,
                    // exit 0 (matching bluesim.tcl)
                    f @ ("-s" | "-ss" | "-r" | "-cc") => {
                        println!(
                            "Error: {f} is deprecated in favor of scriptable debug"
                        );
                        println!("See entry #031 in the KPnS document.");
                        return usage_exit();
                    }
                    "-h" | "-help" | "--help" => return usage_exit(),
                    "-v" => {
                        println!(
                            "bsim3 {} (Bluesim 3 runtime)",
                            env!("CARGO_PKG_VERSION")
                        );
                        return ExitCode::SUCCESS;
                    }
                    "--script_name" => {
                        let _ = it.next();
                    }
                    "--code" => {
                        code_so = it.next().map(|s| s.to_string());
                    }
                    // artifacts pin their split threshold (arena layout)
                    "--split" => {
                        if let Some(n) = it.next() {
                            std::env::set_var("BSIM3_JIT_SPLIT", n);
                        }
                    }
                    "--creation_time" => {
                        let _ = it.next();
                    }
                    // -c/-f collect script commands (bluesim.tcl:94-124);
                    // a later deprecated flag still wins (exit 0 above)
                    "-c" => match it.next() {
                        Some(cmds) => {
                            script_cmds.push_str(cmds);
                            script_cmds.push('\n');
                        }
                        None => {
                            println!("Error: -c requires a command argument");
                            return usage_exit();
                        }
                    },
                    "-f" => match it.next() {
                        Some(f) => match std::fs::read_to_string(f) {
                            Ok(s) => {
                                script_cmds.push_str(&s);
                                script_cmds.push('\n');
                            }
                            Err(e) => {
                                eprintln!("bsim3: {f}: {e}");
                                return ExitCode::from(2);
                            }
                        },
                        None => {
                            println!("Error: -f requires a script filename argument");
                            return usage_exit();
                        }
                    },
                    "-m" => {
                        max_cycles = it
                            .next()
                            .and_then(|n| n.parse::<u64>().ok())
                            .unwrap_or(u64::MAX);
                    }
                    // -V [file]: dump waveforms (default dump.vcd)
                    "-V" => {
                        let takes_arg = it
                            .peek()
                            .map(|n| !n.starts_with('-') && !n.starts_with('+'))
                            .unwrap_or(false);
                        vcd_file = Some(if takes_arg {
                            it.next().unwrap().to_string()
                        } else {
                            "dump.vcd".to_string()
                        });
                    }
                    p if p.starts_with('+') => plusargs.push(p[1..].to_string()),
                    other => {
                        eprintln!("Error: invalid option '{other}'");
                        return ExitCode::from(2);
                    }
                }
            }
            if !script_cmds.is_empty() {
                return run_script(
                    path,
                    max_cycles,
                    &plusargs,
                    vcd_file.as_deref(),
                    code_so.as_deref(),
                    &script_cmds,
                );
            }
            match bsim3_interp::run_file(
                path,
                max_cycles,
                &plusargs,
                vcd_file.as_deref(),
                code_so.as_deref(),
            ) {
                Ok(code) => {
                    use std::io::Write;
                    let _ = std::io::stdout().flush();
                    let _ = std::io::stderr().flush();
                    // bypass atexit teardown: JIT body workers may still
                    // be inside LLVM and would stall process exit
                    unsafe { libc::_exit(code.clamp(0, 255) as i32) }
                }
                Err(e) => {
                    eprintln!("bsim3: {e}");
                    ExitCode::FAILURE
                }
            }
        }
        _ => usage(),
    }
}

/// The scripting subset of bluesim.tcl's `sim` command that the testsuite
/// uses outside bsc.bluesim/interactive: `sim run`/`sim step N` (multi-step
/// resumable, on Interp::advance) plus `sim time`/`sim clock` queries and
/// `puts [...]` printing.  The full interactive surface arrives with the
/// bk_* compat .so (task #20); anything beyond this subset errors out
/// loudly.
/// `bsim3 link --interactive`: produce <base>.so (the bk_* capi model
/// with the BIR embedded via incbin) and <base>, the same bluesim.tcl
/// wrapper the reference emits — `sim load`-able by stock bluetcl and
/// runnable by the interactive testsuite unchanged.
fn link_interactive(bir_path: &str, base: &str, top: &str) -> ExitCode {
    let fail = |m: String| {
        eprintln!("bsim3 link --interactive: {m}");
        ExitCode::FAILURE
    };
    // the capi staticlib: env override, then alongside the binary
    let lib = std::env::var("BSIM3_CAPI_LIB").ok().map(std::path::PathBuf::from).or_else(|| {
        let exe = std::env::current_exe().ok()?;
        let d = exe.parent()?;
        [d.join("libbsim3_capi.a"), d.join("../lib/libbsim3_capi.a")]
            .into_iter()
            .find(|p| p.exists())
    });
    let Some(lib) = lib else {
        return fail(
            "libbsim3_capi.a not found (set BSIM3_CAPI_LIB or install it              next to the bsim3 binary)"
                .into(),
        );
    };
    let Ok(bir_abs) = std::path::Path::new(bir_path).canonicalize() else {
        return fail(format!("cannot resolve {bir_path}"));
    };
    let tmp = std::env::temp_dir().join(format!("bsim3-capi-{}", std::process::id()));
    if let Err(e) = std::fs::create_dir_all(&tmp) {
        return fail(format!("{}: {e}", tmp.display()));
    }
    let shim_s = tmp.join("bir.s");
    let shim_c = tmp.join("shim.c");
    let map = tmp.join("export.map");
    let w = |p: &std::path::Path, c: String| std::fs::write(p, c);
    if let Err(e) = w(
        &shim_s,
        format!(
            r##"	.section .rodata
	.align 8
	.globl bsim3_bir_start
bsim3_bir_start:
	.incbin "{}"
	.globl bsim3_bir_end
bsim3_bir_end:
"##,
            bir_abs.display()
        ),
    ) {
        return fail(format!("write {}: {e}", shim_s.display()));
    }
    if let Err(e) = w(
        &shim_c,
        format!(
            r##"/* generated by bsim3 link --interactive */
typedef struct {{
    const unsigned char* bir_ptr;
    unsigned long        bir_len;
    const char*          top;
}} Model;
extern const unsigned char bsim3_bir_start[], bsim3_bir_end[];
static Model M;
void* new_MODEL_{top}(void) {{
    M.bir_ptr = bsim3_bir_start;
    M.bir_len = (unsigned long)(bsim3_bir_end - bsim3_bir_start);
    M.top = "{top}";
    return &M;
}}
"##
        ),
    ) {
        return fail(format!("write {}: {e}", shim_c.display()));
    }
    if let Err(e) = w(
        &map,
        "{ global: bk_*; bsim3_*; new_MODEL_*; local: *; };\n".into(),
    ) {
        return fail(format!("write {}: {e}", map.display()));
    }
    let so = format!("{base}.so");
    let st = std::process::Command::new("cc")
        .arg("-shared")
        .arg("-fPIC")
        .arg("-o")
        .arg(&so)
        .arg(&shim_c)
        .arg(&shim_s)
        .arg("-Wl,--whole-archive")
        .arg(&lib)
        .arg("-Wl,--no-whole-archive")
        .arg("-Wl,-Bsymbolic")
        .arg(format!("-Wl,--version-script={}", map.display()))
        .arg("-lpthread")
        .arg("-ldl")
        .arg("-lm")
        .status();
    match st {
        Ok(s) if s.success() => {}
        Ok(s) => return fail(format!("cc exited {s}")),
        Err(e) => return fail(format!("cc: {e}")),
    }
    let _ = std::fs::remove_dir_all(&tmp);
    // the reference's wrapper, verbatim shape (bsc.hs writeBluesimWrapper)
    let wrapper = format!(
        r##"#!/bin/sh

BLUESPECDIR=`echo 'puts $env(BLUESPECDIR)' | bluetcl`

for arg in $@
do
  if (test "$arg" = "-h")
  then
    exec $BLUESPECDIR/tcllib/bluespec/bluesim.tcl $0.so {top} --script_name `basename $0` -h
  fi
done
exec $BLUESPECDIR/tcllib/bluespec/bluesim.tcl $0.so {top} --script_name `basename $0` "$@"
"##
    );
    if let Err(e) = std::fs::write(base, wrapper) {
        return fail(format!("write {base}: {e}"));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let _ = std::fs::set_permissions(base, std::fs::Permissions::from_mode(0o755));
    }
    println!("bsim3 link: interactive model written: {so}");
    ExitCode::SUCCESS
}

fn run_script(
    path: &str,
    max_cycles: u64,
    plusargs: &[String],
    vcd: Option<&str>,
    code: Option<&str>,
    script: &str,
) -> ExitCode {
    let mut interp = match bsim3_interp::load_file(path, plusargs, vcd) {
        Ok(i) => i,
        Err(e) => {
            eprintln!("bsim3: {e}");
            return ExitCode::FAILURE;
        }
    };
    if let Some(so) = code {
        interp.aot_request_code(so.into());
    }
    for raw in script.split(['\n', ';']) {
        let cmd = raw.trim();
        if cmd.is_empty() {
            continue;
        }
        // `puts [sim x]`: evaluate the bracketed command and print it
        let (do_print, inner) = match cmd.strip_prefix("puts ") {
            Some(rest) => {
                let r = rest.trim();
                let r = r
                    .strip_prefix('[')
                    .and_then(|r| r.strip_suffix(']'))
                    .unwrap_or(r);
                (true, r.trim().to_string())
            }
            None => (false, cmd.to_string()),
        };
        let words: Vec<&str> = inner.split_whitespace().collect();
        let out = match words.as_slice() {
            ["sim", "run"] | ["sim", "step"] | ["sim", "step", _] => {
                // the reference kernel refuses to continue after $finish
                if interp.is_finished() {
                    let what =
                        if words[1] == "run" { "run anymore" } else { "step" };
                    eprintln!("Error: $finish has been called -- cannot {what}");
                    interp.finish();
                    return ExitCode::FAILURE;
                }
                // step N advances N default-clock posedges from the
                // current cycle cursor; run goes to the -m limit
                let target = match words.as_slice() {
                    ["sim", "step", n] => {
                        interp.cycles().saturating_add(n.parse::<u64>().unwrap_or(1))
                    }
                    ["sim", "step"] => interp.cycles() + 1,
                    _ => max_cycles,
                };
                interp.advance(target.min(max_cycles));
                String::new()
            }
            ["sim", "time"] => format!("{}", interp.now()),
            ["sim", "clock"] => interp
                .clock_info()
                .iter()
                .enumerate()
                .map(|(i, c)| {
                    format!(
                        "{{{} {} {} {} {} {} {} {} {} {}}}",
                        i,
                        (i == 0) as u32,
                        c.name,
                        c.initial_val as u32,
                        c.first_edge,
                        c.low_dur,
                        c.high_dur,
                        c.cycles,
                        c.cur_val as u32,
                        c.last_edge,
                    )
                })
                .collect::<Vec<_>>()
                .join(" "),
            ["sim", "config", "interactive"] => String::new(),
            _ => {
                eprintln!(
                    "bsim3: unsupported -c/-f command {cmd:?} \
                     (the interactive surface is not yet implemented)"
                );
                return ExitCode::from(2);
            }
        };
        if do_print {
            println!("{out}");
        }
    }
    // end-of-session epilogue: final VCD flush + $fatal exit code
    ExitCode::from(if interp.finish() != 0 { 1 } else { 0 })
}
