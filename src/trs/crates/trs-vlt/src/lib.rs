//! BVI import: the verilate-or-cache pipeline (design of record: the KB
//! draft "KB: BVI-via-Verilator design (trs)", v4 sec 5.2; validated
//! end-to-end by the M0 spike at src/trs/spike/bvi-m0/).
//!
//! `trs link` and `trs run` call [`build_all`] before instantiating a
//! design that carries `InstanceKind::Bvi` contracts.  Per contract
//! class -- (verilator version, shim-generator revision, contract
//! shape, typed parameters, defines, resolved top file) -- the pipeline
//! resolves sources, extracts model metadata through the versioned
//! adapters, applies the inspection refusals (delays, DPI), generates
//! the engine-neutral shim, builds a shared object, and caches it
//! content-addressed over the depfile closure with a per-class lock.
//!
//! The build is `--no-timing`; only the metadata INSPECTION dump runs
//! `--timing` (so delay constructs survive into the dumped AST -- an M0
//! discovery; see meta.rs).

use std::fmt;
use std::os::unix::io::AsRawFd;
use std::path::{Path, PathBuf};
use std::process::Command;

use trs_ir::bvi::{BviContract, BviParamValue};
use trs_ir::Design;

pub mod json;
pub mod meta;
pub mod resolve;
pub mod sha256;
pub mod shim;

// ---------------------------------------------------------------
// Error taxonomy

#[derive(Debug)]
pub enum VltError {
    /// A design shape or model property v1 refuses, with a stable tag
    /// (delay, dpi, contract-mismatch, param-type, ...).
    Refuse { tag: String, detail: String },
    /// A toolchain step failed (verilator, make, g++, dlopen).
    Tool { stage: String, detail: String },
    /// Source resolution failed.
    Resolve { detail: String },
}

impl VltError {
    pub fn refuse(tag: &str, detail: String) -> Self {
        VltError::Refuse { tag: tag.into(), detail }
    }
    pub fn tool(stage: &str, detail: String) -> Self {
        VltError::Tool { stage: stage.into(), detail }
    }
    pub fn resolve(detail: String) -> Self {
        VltError::Resolve { detail }
    }
}

impl fmt::Display for VltError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VltError::Refuse { tag, detail } => {
                write!(f, "REFUSE({tag}): {detail}")
            }
            VltError::Tool { stage, detail } => {
                write!(f, "{stage} failed: {detail}")
            }
            VltError::Resolve { detail } => write!(f, "source resolution: {detail}"),
        }
    }
}

impl std::error::Error for VltError {}

// ---------------------------------------------------------------
// Options

#[derive(Debug, Clone)]
pub struct BuildOptions {
    pub verilator: PathBuf,
    pub cache_dir: PathBuf,
    /// Extra search dirs, tried BEFORE the contract's own vpath.
    pub extra_vpath: Vec<PathBuf>,
    /// Explicitly named source files; override all path search.
    pub extra_vfiles: Vec<PathBuf>,
    pub verbose: bool,
}

impl BuildOptions {
    /// Defaults per the design's provisional Q3 answer: per-user cache
    /// (~/.cache/trs) with TRS_VLT_CACHE override; TRS_VERILATOR picks
    /// the binary (default: `verilator` on PATH).
    pub fn from_env() -> Self {
        let verilator = std::env::var_os("TRS_VERILATOR")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("verilator"));
        let cache_dir = std::env::var_os("TRS_VLT_CACHE")
            .map(PathBuf::from)
            .unwrap_or_else(|| {
                std::env::var_os("XDG_CACHE_HOME")
                    .map(PathBuf::from)
                    .unwrap_or_else(|| {
                        let home = std::env::var_os("HOME")
                            .map(PathBuf::from)
                            .unwrap_or_else(|| PathBuf::from("."));
                        home.join(".cache")
                    })
                    .join("trs")
            });
        BuildOptions {
            verilator,
            cache_dir,
            extra_vpath: Vec::new(),
            extra_vfiles: Vec::new(),
            verbose: false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct BuiltModel {
    pub so_path: PathBuf,
    /// sha256[:16] of the contract JSON; must equal the hash the loaded
    /// model reports through vlt_contract.
    pub contract_hash: String,
    pub cached: bool,
    pub class: String,
    pub verilog_name: String,
}

// ---------------------------------------------------------------
// Typed -G parameter serialization (v4 sec 4.5: semantics, not text)

fn serialize_param(
    name: &str,
    v: &BviParamValue,
    strings: &[String],
) -> Result<String, VltError> {
    let s = |id: u32| strings.get(id as usize).map(String::as_str).unwrap_or("");
    Ok(match v {
        BviParamValue::IntSigned { value, .. } => format!("-G{name}={value}"),
        BviParamValue::Bits { width, hex } => {
            format!("-G{name}={width}'h{}", s(*hex))
        }
        BviParamValue::Str(sid) => {
            let esc = s(*sid).replace('\\', "\\\\").replace('"', "\\\"");
            format!("-G{name}=\"{esc}\"")
        }
        BviParamValue::Real(d) => format!("-G{name}={d:?}"),
    })
}

// ---------------------------------------------------------------
// Per-class file lock (advisory flock; released on drop)

struct ClassLock {
    _file: std::fs::File,
}

impl ClassLock {
    fn acquire(dir: &Path) -> Result<ClassLock, VltError> {
        let path = dir.join(".lock");
        let file = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .open(&path)
            .map_err(|e| VltError::tool("cache lock", format!("{}: {e}", path.display())))?;
        let rc = unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX) };
        if rc != 0 {
            return Err(VltError::tool(
                "cache lock",
                format!("flock {}: {}", path.display(), std::io::Error::last_os_error()),
            ));
        }
        Ok(ClassLock { _file: file })
    }
}

// ---------------------------------------------------------------
// Depfile manifest: content-address the transitive source closure

fn parse_depfiles(obj: &Path) -> Vec<PathBuf> {
    let mut deps: Vec<PathBuf> = Vec::new();
    if let Ok(rd) = std::fs::read_dir(obj) {
        for ent in rd.flatten() {
            let p = ent.path();
            if p.extension().and_then(|e| e.to_str()) != Some("d") {
                continue;
            }
            let Ok(text) = std::fs::read_to_string(&p) else { continue };
            // "target: dep dep \\\n dep ..." -- possibly several rules
            for rule in text.split(':').skip(1) {
                for tok in rule.split_whitespace() {
                    if tok == "\\" {
                        continue;
                    }
                    let dep = PathBuf::from(tok);
                    // only source-tree files matter; generated files in
                    // the obj dir would self-invalidate the manifest
                    if dep.is_file() && !dep.starts_with(obj) && !deps.contains(&dep) {
                        deps.push(dep);
                    }
                }
            }
        }
    }
    deps.sort();
    deps
}

fn hash_file(p: &Path) -> Option<String> {
    std::fs::read(p).ok().map(|b| sha256::digest_hex(&b))
}

fn write_manifest(path: &Path, deps: &[PathBuf]) -> Result<(), VltError> {
    let mut out = String::new();
    for d in deps {
        let h = hash_file(d).unwrap_or_default();
        out.push_str(&format!("{h}  {}\n", d.display()));
    }
    std::fs::write(path, out)
        .map_err(|e| VltError::tool("manifest write", format!("{}: {e}", path.display())))
}

fn manifest_valid(path: &Path) -> bool {
    let Ok(text) = std::fs::read_to_string(path) else {
        return false;
    };
    for line in text.lines() {
        let Some((h, p)) = line.split_once("  ") else {
            return false;
        };
        match hash_file(Path::new(p)) {
            Some(now) if now == h => {}
            _ => return false,
        }
    }
    true
}

// ---------------------------------------------------------------
// License packaging: the artifact embeds the Verilator runtime

const NOTICE: &str = "\
This directory contains a shared object built by trs from a Verilog
design using Verilator.  The object embeds the Verilator runtime
(verilated.cpp and headers), which is licensed under
LGPL-3.0-only OR Artistic-2.0 (see the COPYING and COPYING.LESSER
files in the Verilator installation).  The generated model code and
the trs shim are derived from the user's Verilog sources and the trs
contract respectively.  Redistribution of this object must comply
with the Verilator runtime license.
";

// ---------------------------------------------------------------
// The pipeline

fn run_logged(mut cmd: Command, stage: &str) -> Result<std::process::Output, VltError> {
    let out = cmd
        .output()
        .map_err(|e| VltError::tool(stage, e.to_string()))?;
    if !out.status.success() {
        let mut detail = String::from_utf8_lossy(&out.stderr).to_string();
        if detail.trim().is_empty() {
            detail = String::from_utf8_lossy(&out.stdout).to_string();
        }
        return Err(VltError::tool(stage, detail));
    }
    Ok(out)
}

/// Build (or reuse from cache) the verilated model for one contract.
pub fn build_model(
    c: &BviContract,
    strings: &[String],
    opts: &BuildOptions,
) -> Result<BuiltModel, VltError> {
    let s = |id: u32| strings.get(id as usize).map(String::as_str).unwrap_or("");
    let top = s(c.verilog_name).to_string();

    // ---- resolve sources
    let mut vpath: Vec<PathBuf> = opts.extra_vpath.clone();
    vpath.extend(c.vpath.iter().map(|&id| PathBuf::from(s(id))));
    let vpath = resolve::clean_dirs(&vpath);
    let mut vfiles: Vec<PathBuf> = opts.extra_vfiles.clone();
    vfiles.extend(c.vfiles.iter().map(|&id| PathBuf::from(s(id))));
    let top_file = resolve::resolve_top(&top, &vpath, &vfiles)?;
    let top_file = top_file
        .canonicalize()
        .map_err(|e| VltError::resolve(format!("{}: {e}", top_file.display())))?;

    // ---- typed params and defines
    let mut gparams = Vec::new();
    for prm in &c.params {
        gparams.push(serialize_param(s(prm.name), &prm.value, strings)?);
    }
    let defines: Vec<(String, Option<String>)> = c
        .defines
        .iter()
        .map(|(k, v)| (s(*k).to_string(), v.map(|v| s(v).to_string())))
        .collect();

    // ---- class key
    let (vmaj, vmin, vfull) = meta::verilator_version(&opts.verilator)?;
    let cjson = shim::contract_json(c, strings);
    let mut keysrc = String::new();
    keysrc.push_str(&format!("shimgen={}\n", shim::SHIMGEN_REV));
    keysrc.push_str(&format!("verilator={vfull}\n"));
    keysrc.push_str(&format!("top={top}\n"));
    keysrc.push_str(&format!("topfile={}\n", top_file.display()));
    keysrc.push_str(&format!("contract={cjson}\n"));
    for g in &gparams {
        keysrc.push_str(&format!("gparam={g}\n"));
    }
    for (k, v) in &defines {
        keysrc.push_str(&format!("define={k}={}\n", v.as_deref().unwrap_or("")));
    }
    for d in &vpath {
        keysrc.push_str(&format!("vpath={}\n", d.display()));
    }
    let class = sha256::digest_hex(keysrc.as_bytes())[..32].to_string();

    let class_dir = opts.cache_dir.join("vlt").join(&class);
    std::fs::create_dir_all(&class_dir).map_err(|e| {
        VltError::tool("cache dir", format!("{}: {e}", class_dir.display()))
    })?;
    let _lock = ClassLock::acquire(&class_dir)?;

    let so_path = class_dir.join(format!("lib{top}_shim.vlt.so"));
    let manifest = class_dir.join("manifest");

    // expected contract hash (recomputed cheaply; also embedded in the
    // shim at build time)
    let expect_hash = sha256::digest_hex(cjson.as_bytes())[..16].to_string();

    // ---- cache hit: manifest present AND every dep content unchanged
    if so_path.is_file() && manifest.is_file() && manifest_valid(&manifest) {
        dlopen_check(&so_path, &expect_hash)?;
        return Ok(BuiltModel {
            so_path,
            contract_hash: expect_hash,
            cached: true,
            class,
            verilog_name: top,
        });
    }

    if opts.verbose {
        eprintln!("trs-vlt: verilating {top} (class {class}, verilator {vmaj}.{vmin:03})");
    }

    // ---- metadata inspection (versioned adapters; --timing dump)
    let meta_dir = class_dir.join("meta");
    let m = meta::extract(
        &opts.verilator,
        &top,
        std::slice::from_ref(&top_file),
        &vpath,
        &defines,
        &gparams,
        &meta_dir,
    )?;
    if m.has_delay {
        return Err(VltError::refuse(
            "delay",
            format!("{top} contains delay constructs (not supported)"),
        ));
    }
    if m.has_dpi == Some(true) {
        return Err(VltError::refuse(
            "dpi",
            format!("{top} imports or exports DPI (not supported)"),
        ));
    }

    let decl_path = class_dir.join("trs_printf_decl.h");
    std::fs::write(&decl_path, shim::PRINTF_DECL_H)
        .map_err(|e| VltError::tool("shim write", format!("{}: {e}", decl_path.display())))?;

    // ---- verilate (--no-timing build) with depfiles.  This runs
    // BEFORE shim generation so the __Dpi.h backstop below refuses DPI
    // models with the right tag on XML-era versions (whose metadata
    // cannot tell) before any contract-vs-model port check.
    let obj = class_dir.join("obj");
    let cflags = format!(
        "-DVL_USER_FATAL -DVL_USER_FINISH -DVL_PRINTF=trs_vlt_printf -include {} -fPIC",
        decl_path.display()
    );
    let mut cmd = Command::new(&opts.verilator);
    cmd.arg("--cc")
        .arg("--no-timing")
        .arg("--x-assign")
        .arg("0")
        .arg("--x-initial")
        .arg("0")
        .arg("-O2")
        .arg("--assert")
        .arg("--MMD")
        .arg("--top-module")
        .arg(&top)
        .arg("-Mdir")
        .arg(&obj)
        .arg("-CFLAGS")
        .arg(&cflags);
    for d in &vpath {
        cmd.arg("-y").arg(d);
    }
    cmd.arg("+libext+.v+.sv");
    for (k, v) in &defines {
        match v {
            Some(v) => cmd.arg(format!("-D{k}={v}")),
            None => cmd.arg(format!("-D{k}")),
        };
    }
    for g in &gparams {
        cmd.arg(g);
    }
    cmd.arg(&top_file);
    run_logged(cmd, "verilate")?;

    // ---- DPI backstop: V<top>__Dpi.h emission is deterministic on
    // every version (5.020's XML has no DPI marker at all)
    if obj.join(format!("V{top}__Dpi.h")).is_file() {
        return Err(VltError::refuse(
            "dpi",
            format!("{top} imports or exports DPI (V{top}__Dpi.h emitted)"),
        ));
    }

    // ---- shim generation (includes contract-vs-model checks)
    let (shim_cpp, chash) = shim::generate(c, strings, &m)?;
    debug_assert_eq!(chash, expect_hash);
    let shim_path = class_dir.join("shim.cpp");
    std::fs::write(&shim_path, shim_cpp)
        .map_err(|e| VltError::tool("shim write", format!("{}: {e}", shim_path.display())))?;

    // ---- compile the model library
    let mut mk = Command::new("make");
    mk.arg("-s")
        .arg("-C")
        .arg(&obj)
        .arg("-f")
        .arg(format!("V{top}.mk"))
        .arg(format!("V{top}__ALL.a"))
        .arg("verilated.o")
        .arg("verilated_threads.o");
    run_logged(mk, "model build")?;

    // ---- link the shim into a shared object
    let vroot = String::from_utf8_lossy(
        &run_logged(
            {
                let mut c = Command::new(&opts.verilator);
                c.arg("--getenv").arg("VERILATOR_ROOT");
                c
            },
            "verilator root probe",
        )?
        .stdout,
    )
    .trim()
    .to_string();
    let mut ld = Command::new("g++");
    ld.arg("-shared")
        .arg("-fPIC")
        .arg("-O2")
        .arg("-std=c++17")
        .arg("-DVL_USER_FATAL")
        .arg("-DVL_USER_FINISH")
        .arg("-DVL_PRINTF=trs_vlt_printf")
        .arg("-include")
        .arg(&decl_path)
        .arg("-I")
        .arg(&obj)
        .arg("-I")
        .arg(format!("{vroot}/include"))
        .arg("-I")
        .arg(format!("{vroot}/include/vltstd"))
        .arg(&shim_path)
        .arg(obj.join(format!("V{top}__ALL.a")))
        .arg(obj.join("verilated.o"))
        .arg(obj.join("verilated_threads.o"))
        .arg("-lpthread")
        .arg("-lz")
        .arg("-o")
        .arg(&so_path);
    run_logged(ld, "shim link")?;

    // ---- license notice, manifest (manifest LAST: its presence marks
    // the class entry valid), load check
    let _ = std::fs::write(class_dir.join("NOTICE"), NOTICE);
    let mut deps = parse_depfiles(&obj);
    if !deps.contains(&top_file) {
        deps.push(top_file.clone());
    }
    deps.sort();
    write_manifest(&manifest, &deps)?;
    dlopen_check(&so_path, &expect_hash)?;

    Ok(BuiltModel {
        so_path,
        contract_hash: expect_hash,
        cached: false,
        class,
        verilog_name: top,
    })
}

/// dlopen the built model and confirm it reports the expected contract
/// hash through vlt_contract -- the load-time identity check that model
/// substitution (--bvi-model) also goes through.
fn dlopen_check(so: &Path, expect_hash: &str) -> Result<(), VltError> {
    use std::ffi::{CStr, CString};
    let cpath = CString::new(so.display().to_string())
        .map_err(|_| VltError::tool("dlopen", "path contains NUL".into()))?;
    let handle = unsafe { libc::dlopen(cpath.as_ptr(), libc::RTLD_NOW | libc::RTLD_LOCAL) };
    if handle.is_null() {
        let err = unsafe { CStr::from_ptr(libc::dlerror()) };
        return Err(VltError::tool(
            "dlopen",
            format!("{}: {}", so.display(), err.to_string_lossy()),
        ));
    }
    let sym = CString::new("vlt_contract").unwrap();
    let f = unsafe { libc::dlsym(handle, sym.as_ptr()) };
    let result = if f.is_null() {
        Err(VltError::tool(
            "dlopen",
            format!("{}: no vlt_contract symbol", so.display()),
        ))
    } else {
        let getc: extern "C" fn() -> *const libc::c_char =
            unsafe { std::mem::transmute(f) };
        let text = unsafe { CStr::from_ptr(getc()) }.to_string_lossy().to_string();
        let want = format!("\"hash\":\"{expect_hash}\"");
        if text.contains(&want) {
            Ok(())
        } else {
            Err(VltError::refuse(
                "contract-mismatch",
                format!(
                    "{}: loaded model's contract hash does not match the design \
                     (rebuilt from a different contract?)",
                    so.display()
                ),
            ))
        }
    };
    unsafe { libc::dlclose(handle) };
    result
}

/// Build every distinct BVI model class in a design.  Returns one entry
/// per (module, instance) carrying the built model; classes are shared,
/// so two instances of the same import build once.
pub fn build_all(
    design: &Design,
    opts: &BuildOptions,
) -> Result<Vec<(String, BuiltModel)>, VltError> {
    let mut out = Vec::new();
    let mut done: Vec<(String, BuiltModel)> = Vec::new();
    for m in &design.modules {
        for inst in &m.instances {
            if let trs_ir::InstanceKind::Bvi(c) = &inst.kind {
                let iname = design.strings[inst.name as usize].clone();
                let cjson = shim::contract_json(c, &design.strings);
                let key = sha256::digest_hex(cjson.as_bytes());
                let built = match done.iter().find(|(k, _)| *k == key) {
                    Some((_, b)) => b.clone(),
                    None => {
                        let b = build_model(c, &design.strings, opts)?;
                        done.push((key, b.clone()));
                        b
                    }
                };
                out.push((iname, built));
            }
        }
    }
    Ok(out)
}
