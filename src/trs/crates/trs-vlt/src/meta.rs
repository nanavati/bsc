//! Versioned Verilator metadata adapters (design v4 sec 5.2 item 2).
//!
//! The model metadata -- port name mapping (origName -> possibly
//! mangled member name), widths, directions, parameter list, the delay
//! presence that selects the --timing build mode, and the DPI presence
//! that powers the DPI refusal -- is read from a frontend dump.  Two formats, selected by probing the binary:
//!   XML  (--xml-only): present through 5.045 (the 5.020 floor uses it).
//!   JSON (--json-only): the replacement from 5.046 onward (5.046+
//!         hard-reject --xml-only; verified on source-built 5.050).
//! One normalized `ModelMeta` comes back either way; nothing downstream
//! looks at the raw dump.
//!
//! M0 discoveries baked in here:
//! - The inspection dump runs with --timing so delay constructs SURVIVE
//!   into the AST; a --no-timing dump discards them before dumping and
//!   -Werror-*DLY stays silent in dump-only mode, so a --no-timing dump
//!   cannot detect delays.  (has_delay selects whether the model BUILD
//!   runs --timing or --no-timing.)
//! - 5.020's XML carries NO DPI marker at all; `has_dpi: None` means
//!   UNKNOWN and the builder must backstop by checking for
//!   V<top>__Dpi.h emission after the real --cc run.

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
    /// None = this format cannot tell (XML on old releases); the
    /// builder MUST apply the __Dpi.h backstop.
    pub has_dpi: Option<bool>,
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

fn pick_format(major: u32, minor: u32) -> &'static str {
    if (major, minor) < (5, 46) {
        "xml"
    } else {
        "json"
    }
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
    let (major, minor, _full) = verilator_version(vlt)?;
    let fmt = pick_format(major, minor);
    std::fs::create_dir_all(mdir)
        .map_err(|e| VltError::tool("meta dir", format!("{}: {e}", mdir.display())))?;
    let mut cmd = Command::new(vlt);
    cmd.arg("--cc")
        .arg("--timing")
        .arg(format!("--{fmt}-only"))
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
        return Err(VltError::tool(
            "metadata dump",
            String::from_utf8_lossy(&out.stderr).to_string(),
        ));
    }
    let dump = find_dump(mdir, fmt)?;
    let text = std::fs::read_to_string(&dump)
        .map_err(|e| VltError::tool("metadata read", format!("{}: {e}", dump.display())))?;
    if fmt == "xml" {
        parse_xml(&text, top)
    } else {
        parse_json(&text, top)
    }
}

fn find_dump(mdir: &Path, fmt: &str) -> Result<PathBuf, VltError> {
    let mut candidates = Vec::new();
    let rd = std::fs::read_dir(mdir)
        .map_err(|e| VltError::tool("meta dir", format!("{}: {e}", mdir.display())))?;
    for ent in rd.flatten() {
        let p = ent.path();
        let name = p.file_name().and_then(|n| n.to_str()).unwrap_or("");
        let hit = match fmt {
            "xml" => name.ends_with(".xml"),
            _ => name.ends_with(".tree.json") || name.ends_with(".json"),
        };
        if hit {
            candidates.push(p);
        }
    }
    // prefer .tree.json over .meta.json when both exist
    candidates.sort_by_key(|p| {
        let n = p.file_name().and_then(|n| n.to_str()).unwrap_or("").to_string();
        (!n.ends_with(".tree.json"), n)
    });
    candidates
        .into_iter()
        .next()
        .ok_or_else(|| VltError::tool("metadata dump", format!("no {fmt} dump in {}", mdir.display())))
}

// ---------------------------------------------------------------
// XML adapter (string scanning: the dump is machine-generated with
// quoted attributes and no nested same-name tags in what we read)

fn tag_attrs(tag: &str) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let b = tag.as_bytes();
    let mut i = 0;
    while i < b.len() {
        // find `key="value"`
        if b[i].is_ascii_alphabetic() || b[i] == b'_' {
            let ks = i;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            if i < b.len() && b[i] == b'=' && i + 1 < b.len() && b[i + 1] == b'"' {
                let ke = i;
                i += 2;
                let vs = i;
                while i < b.len() && b[i] != b'"' {
                    i += 1;
                }
                out.push((tag[ks..ke].to_string(), tag[vs..i].to_string()));
            }
        }
        i += 1;
    }
    out
}

fn scan_tags<'a>(text: &'a str, tag: &str) -> Vec<&'a str> {
    let open = format!("<{tag} ");
    let mut out = Vec::new();
    let mut rest = text;
    while let Some(pos) = rest.find(&open) {
        let after = &rest[pos..];
        if let Some(end) = after.find('>') {
            out.push(&after[..end]);
            rest = &after[end..];
        } else {
            break;
        }
    }
    out
}

fn parse_xml(text: &str, top: &str) -> Result<ModelMeta, VltError> {
    // dtype table
    let mut widths: Vec<(String, u32)> = Vec::new();
    for t in scan_tags(text, "basicdtype") {
        let attrs = tag_attrs(t);
        let get = |k: &str| attrs.iter().find(|(a, _)| a == k).map(|(_, v)| v.as_str());
        let id = match get("id") {
            Some(i) => i.to_string(),
            None => continue,
        };
        let w = match (get("left"), get("right")) {
            (Some(l), Some(r)) => {
                let l: i64 = l.parse().unwrap_or(0);
                let r: i64 = r.parse().unwrap_or(0);
                ((l - r).unsigned_abs() as u32) + 1
            }
            _ => 1,
        };
        widths.push((id, w));
    }
    let width_of = |id: &str| {
        widths
            .iter()
            .find(|(i, _)| i == id)
            .map(|(_, w)| *w)
            .unwrap_or(1)
    };

    // scope to the top module element
    let mut ports = Vec::new();
    let mut params = Vec::new();
    let mut found_top = false;
    for chunk in text.split("<module ") {
        let head_end = match chunk.find('>') {
            Some(e) => e,
            None => continue,
        };
        let head = &chunk[..head_end];
        let attrs = tag_attrs(head);
        let name = attrs
            .iter()
            .find(|(a, _)| a == "name")
            .map(|(_, v)| v.as_str());
        if name != Some(top) {
            continue;
        }
        found_top = true;
        for t in scan_tags(chunk, "var") {
            let attrs = tag_attrs(t);
            let get =
                |k: &str| attrs.iter().find(|(a, _)| a == k).map(|(_, v)| v.as_str());
            // real module ports carry pinIndex; a dir= without it is a
            // function/task argument (DPI import args included) nested
            // inside the module chunk -- verified against 5.020's dump
            if get("dir").is_some() && get("pinIndex").is_none() {
                continue;
            }
            if let Some(dir) = get("dir") {
                let d = match dir {
                    "input" => PortDir::Input,
                    "output" => PortDir::Output,
                    _ => PortDir::Inout,
                };
                let name = get("name").unwrap_or("").to_string();
                ports.push(MetaPort {
                    orig_name: get("origName").unwrap_or(&name).to_string(),
                    name,
                    dir: d,
                    width: get("dtype_id").map(width_of).unwrap_or(1),
                });
            } else if get("param") == Some("true") || get("vartype") == Some("parameter") {
                let name = get("name").unwrap_or("").to_string();
                params.push(get("origName").unwrap_or(&name).to_string());
            }
        }
    }
    if !found_top {
        return Err(VltError::tool(
            "metadata parse",
            format!("top module {top:?} not found in XML dump"),
        ));
    }
    Ok(ModelMeta {
        format: "xml",
        ports,
        params,
        // any <delay> element = a real delay in the timed AST
        // (<assigndly> is any NBA and does NOT count)
        has_delay: text.contains("<delay"),
        has_dpi: None,
        }
    )
}

// ---------------------------------------------------------------
// JSON adapter (5.046+)

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
        has_dpi: Some(has_dpi),
    })
}
