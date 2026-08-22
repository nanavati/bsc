//! Verilator metadata adapter (design v4 sec 5.2 item 2; JSON-only
//! since the pinned-Verilator floor, 2026-08-22).
//!
//! The model metadata -- port name mapping (origName -> possibly
//! mangled member name), widths, directions, parameter list, the delay
//! presence that selects the --timing build mode, and the DPI presence
//! that powers the DPI refusal -- is read from the `--json-only`
//! frontend dump (Verilator >= 5.046; the FLOOR is checked by
//! CAPABILITY, not version string: a verilator that rejects the option
//! produces a clear floor error).  The dump schema is documented as
//! unstable between releases, so the pin is the real guarantee --
//! re-run the r3 battery on any pin change.  Drift failure modes are
//! loud: port drift -> contract-mismatch refusal, missed delays ->
//! Verilator's own NOTIMING error, missed DPI -> the version-proof
//! V<top>__Dpi.h backstop in the builder (kept for exactly this).
//!
//! M0 discovery baked in: the inspection dump runs with --timing so
//! delay constructs SURVIVE into the AST; a --no-timing dump discards
//! them before dumping, so it cannot power delay detection.
//! (has_delay selects whether the model BUILD runs --timing or
//! --no-timing.)

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::json::{self, Value};
use crate::VltError;

#[derive(Debug, Clone)]
pub struct MetaPort {
    /// Verilator's member name (possibly mangled).
    pub name: String,
    /// The source-level port name; contract ports match against this.
    pub orig_name: String,
    pub dir: PortDir,
    pub width: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PortDir {
    Input,
    Output,
    Inout,
}

#[derive(Debug, Clone)]
pub struct ModelMeta {
    pub format: &'static str,
    pub ports: Vec<MetaPort>,
    pub params: Vec<String>,
    pub has_delay: bool,
    pub has_dpi: bool,
}

pub fn verilator_version(vlt: &Path) -> Result<(u32, u32, String), VltError> {
    let out = Command::new(vlt)
        .arg("--version")
        .output()
        .map_err(|e| VltError::tool("version probe", format!("{}: {e}", vlt.display())))?;
    let text = String::from_utf8_lossy(&out.stdout).trim().to_string();
    // "Verilator 5.020 2023-10-29 rev ..."
    let mut major = 0u32;
    let mut minor = 0u32;
    for tok in text.split_whitespace() {
        if let Some((a, b)) = tok.split_once('.') {
            if let (Ok(x), Ok(y)) = (a.parse(), b.parse()) {
                major = x;
                minor = y;
                break;
            }
        }
    }
    if major == 0 {
        return Err(VltError::tool(
            "version probe",
            format!("unrecognized --version output: {text:?}"),
        ));
    }
    Ok((major, minor, text))
}

/// Run the inspection dump and parse it.  `gparams` are the typed -G
/// arguments (a -G on an undeclared parameter is a native hard error on
/// every supported version -- no bespoke absent-parameter check).
pub fn extract(
    vlt: &Path,
    top: &str,
    sources: &[PathBuf],
    ydirs: &[PathBuf],
    defines: &[(String, Option<String>)],
    gparams: &[String],
    mdir: &Path,
) -> Result<ModelMeta, VltError> {
    std::fs::create_dir_all(mdir)
        .map_err(|e| VltError::tool("meta dir", format!("{}: {e}", mdir.display())))?;
    let mut cmd = Command::new(vlt);
    cmd.arg("--cc")
        .arg("--timing")
        .arg("--json-only")
        .arg("--top-module")
        .arg(top)
        .arg("-Mdir")
        .arg(mdir);
    for d in ydirs {
        cmd.arg("-y").arg(d);
    }
    cmd.arg("+libext+.v+.sv");
    for (k, v) in defines {
        match v {
            Some(v) => cmd.arg(format!("-D{k}={v}")),
            None => cmd.arg(format!("-D{k}")),
        };
    }
    for g in gparams {
        cmd.arg(g);
    }
    for s in sources {
        cmd.arg(s);
    }
    let out = cmd
        .output()
        .map_err(|e| VltError::tool("metadata dump", e.to_string()))?;
    if !out.status.success() {
        let err = String::from_utf8_lossy(&out.stderr).to_string();
        // capability floor: a verilator without --json-only (< 5.046)
        // rejects the OPTION itself -- report the requirement, not the
        // design
        if err.to_ascii_lowercase().contains("json-only") {
            let found = verilator_version(vlt)
                .map(|(_, _, full)| full)
                .unwrap_or_else(|_| "unknown".into());
            return Err(VltError::tool(
                "verilator floor",
                format!(
                    "{} does not support --json-only metadata; trs \
                     requires Verilator >= 5.046 (found: {found}). Point \
                     TRS_VERILATOR at the pinned build.",
                    vlt.display()
                ),
            ));
        }
        return Err(VltError::tool("metadata dump", err));
    }
    let dump = find_dump(mdir)?;
    let text = std::fs::read_to_string(&dump)
        .map_err(|e| VltError::tool("metadata read", format!("{}: {e}", dump.display())))?;
    parse_json(&text, top)
}

fn find_dump(mdir: &Path) -> Result<PathBuf, VltError> {
    let mut candidates = Vec::new();
    let rd = std::fs::read_dir(mdir)
        .map_err(|e| VltError::tool("meta dir", format!("{}: {e}", mdir.display())))?;
    for ent in rd.flatten() {
        let p = ent.path();
        let name = p.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if name.ends_with(".tree.json") || name.ends_with(".json") {
            candidates.push(p);
        }
    }
    // prefer .tree.json over .meta.json when both exist
    candidates.sort_by_key(|p| {
        let n = p.file_name().and_then(|n| n.to_str()).unwrap_or("").to_string();
        (!n.ends_with(".tree.json"), n)
    });
    candidates.into_iter().next().ok_or_else(|| {
        VltError::tool("metadata dump", format!("no json dump in {}", mdir.display()))
    })
}

// ---------------------------------------------------------------
// JSON adapter

fn walk<'a>(v: &'a Value, f: &mut dyn FnMut(&'a Value)) {
    match v {
        Value::Obj(m) => {
            f(v);
            for x in m.values() {
                walk(x, f);
            }
        }
        Value::Arr(items) => {
            for x in items {
                walk(x, f);
            }
        }
        _ => {}
    }
}

fn parse_json(text: &str, top: &str) -> Result<ModelMeta, VltError> {
    let tree = json::parse(text)
        .map_err(|e| VltError::tool("metadata parse", format!("JSON: {e}")))?;

    // pass 1: dtype table (addr-referenced nodes with a bit range like
    // "7:0"; range absent = width 1)
    let mut widths: Vec<(String, u32)> = Vec::new();
    walk(&tree, &mut |n| {
        let is_dtype = n
            .get("type")
            .and_then(|t| t.as_str())
            .map(|t| t.contains("DTYPE"))
            .unwrap_or(false);
        if !is_dtype {
            return;
        }
        let addr = match n.get("addr").and_then(|a| a.as_str()) {
            Some(a) => a.to_string(),
            None => return,
        };
        let w = match n.get("range").and_then(|r| r.as_str()) {
            Some(r) => match r.split_once(':') {
                Some((l, rr)) => {
                    let l: i64 = l.trim().parse().unwrap_or(0);
                    let rr: i64 = rr.trim().parse().unwrap_or(0);
                    ((l - rr).unsigned_abs() as u32) + 1
                }
                None => 1,
            },
            None => 1,
        };
        widths.push((addr, w));
    });
    let width_of = |addr: &str| {
        widths
            .iter()
            .find(|(a, _)| a == addr)
            .map(|(_, w)| *w)
            .unwrap_or(1)
    };

    let mut ports = Vec::new();
    let mut params = Vec::new();
    let mut has_delay = false;
    let mut has_dpi = false;
    let mut found_top = false;

    walk(&tree, &mut |m| {
        if m.get("type").and_then(|t| t.as_str()) != Some("MODULE")
            || m.get("name").and_then(|n| n.as_str()) != Some(top)
        {
            return;
        }
        found_top = true;
        walk(m, &mut |n| {
            let t = n.get("type").and_then(|t| t.as_str()).unwrap_or("");
            if t == "VAR" {
                let direction = n.get("direction").and_then(|d| d.as_str());
                let primary = n
                    .get("isPrimaryIO")
                    .and_then(|b| b.as_bool())
                    .unwrap_or(false);
                if primary && direction.is_some() && direction != Some("NONE") {
                    let name = n
                        .get("verilogName")
                        .or_else(|| n.get("name"))
                        .and_then(|s| s.as_str())
                        .unwrap_or("")
                        .to_string();
                    let orig = n
                        .get("origName")
                        .or_else(|| n.get("name"))
                        .and_then(|s| s.as_str())
                        .unwrap_or(&name)
                        .to_string();
                    let d = match direction.unwrap() {
                        "INPUT" | "input" => PortDir::Input,
                        "OUTPUT" | "output" => PortDir::Output,
                        _ => PortDir::Inout,
                    };
                    let w = n
                        .get("dtypep")
                        .and_then(|a| a.as_str())
                        .map(width_of)
                        .unwrap_or(1);
                    ports.push(MetaPort {
                        name,
                        orig_name: orig,
                        dir: d,
                        width: w,
                    });
                } else if n.get("varType").and_then(|s| s.as_str()) == Some("GPARAM") {
                    let name = n
                        .get("origName")
                        .or_else(|| n.get("name"))
                        .and_then(|s| s.as_str())
                        .unwrap_or("")
                        .to_string();
                    params.push(name);
                }
            }
            if matches!(t, "DELAY" | "DELAYSCHEDULER" | "TIMINGCONTROL") {
                has_delay = true;
            }
            if n.get("dpiImport").and_then(|b| b.as_bool()).unwrap_or(false)
                || n.get("dpiExport").and_then(|b| b.as_bool()).unwrap_or(false)
            {
                has_dpi = true;
            }
        });
    });

    if !found_top {
        return Err(VltError::tool(
            "metadata parse",
            format!("top module {top:?} not found in JSON dump"),
        ));
    }
    Ok(ModelMeta {
        format: "json",
        ports,
        params,
        has_delay,
        has_dpi,
    })
}
