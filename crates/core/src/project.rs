//! Project discovery: which files to analyse, which language, which commit.
//!
//! Safe on hostile repositories: symlinks are never followed, file sizes and
//! counts are capped, and git metadata is read from `.git` directly — running
//! `git` inside an untrusted repository can execute commands through
//! repository-local configuration (`core.fsmonitor`, hooks, ...).

use crate::error::{Error, Result};
use crate::facts::Language;
use crate::paths::to_repo_path;
use crate::process::{RunOptions, run, which};
use regex::Regex;
use serde::Serialize;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Duration;

#[derive(Debug, Clone, Serialize)]
pub struct SourceFile {
    pub path: String,
    #[serde(skip)]
    pub abs: PathBuf,
    pub language: Language,
    pub size: u64,
}

#[derive(Debug, Clone, Serialize)]
pub struct GitInfo {
    pub commit: Option<String>,
    pub branch: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Project {
    pub root: PathBuf,
    pub name: String,
    pub files: Vec<SourceFile>,
    /// Non-source text files considered for secret scanning.
    #[serde(skip)]
    pub text_files: Vec<PathBuf>,
    /// Data exports, dumps and database files (any size), checked for committed personal data.
    #[serde(skip)]
    pub data_files: Vec<PathBuf>,
    /// Source files in a language Proof-It cannot analyse: (path, language).
    pub unsupported: Vec<(String, String)>,
    pub languages: BTreeMap<String, usize>,
    pub git: Option<GitInfo>,
    pub skipped: Vec<(String, String)>,
}

const SKIP_DIRS: [&str; 22] = [
    "node_modules",
    ".git",
    "dist",
    "build",
    "out",
    "coverage",
    ".next",
    ".nuxt",
    ".turbo",
    ".cache",
    "vendor",
    "target",
    "__pycache__",
    ".venv",
    "venv",
    ".proof-it",
    ".lake",
    ".expo",
    "Pods",
    ".gradle",
    "bower_components",
    ".svelte-kit",
];
/// Data exports, dumps and database files.
pub const DATA_EXTS: [&str; 17] =
    ["csv", "tsv", "jsonl", "ndjson", "sql", "dump", "bak", "backup", "sqlite", "sqlite3", "db", "xlsx", "xls", "parquet", "json", "txt", "log"];

/// Files that pin a runtime version (container images, version-manager files),
/// read by the runtime advisory check.
fn is_runtime_pin_file(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower == "dockerfile"
        || lower.starts_with("dockerfile.")
        || lower.ends_with(".dockerfile")
        || lower == "containerfile"
        || matches!(lower.as_str(), ".nvmrc" | ".node-version" | ".tool-versions")
}

const TEXT_EXTS: [&str; 31] = [
    "json",
    "yml",
    "yaml",
    "env",
    "toml",
    "ini",
    "cfg",
    "conf",
    "properties",
    "xml",
    "sh",
    "bash",
    "zsh",
    "tf",
    "tfvars",
    "md",
    "txt",
    "pem",
    "key",
    "sql",
    "gradle",
    "plist",
    // templates (scanned for unescaped output)
    "ejs",
    "hbs",
    "handlebars",
    "pug",
    "jade",
    "njk",
    "html",
    "vue",
    "svelte",
];
pub const MAX_FILE_BYTES: u64 = 2 * 1024 * 1024;
const MAX_FILES: usize = 50_000;

/// Restricted glob (`*`, `**`, literal segments) → anchored regex over repo paths.
/// A bare directory name excludes everything below it.
pub fn glob_to_regex(glob: &str) -> Option<Regex> {
    let mut re = String::from("^");
    let mut chars = glob.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '*' if chars.peek() == Some(&'*') => {
                chars.next();
                if chars.peek() == Some(&'/') {
                    chars.next();
                }
                re.push_str(".*");
            }
            '*' => re.push_str("[^/]*"),
            c => re.push_str(&regex::escape(&c.to_string())),
        }
    }
    re.push_str("(?:/.*)?$");
    Regex::new(&re).ok()
}

pub fn discover(root: &Path, exclude: &[String], languages: &[String]) -> Result<Project> {
    let meta = std::fs::metadata(root).map_err(|e| Error::io(root, e))?;
    if !meta.is_dir() {
        return Err(Error::Usage(format!("not a directory: {}", root.display())));
    }
    let excludes: Vec<Regex> = exclude.iter().filter_map(|g| glob_to_regex(g)).collect();
    let mut p = Project {
        root: root.to_path_buf(),
        name: project_name(root),
        files: vec![],
        text_files: vec![],
        data_files: vec![],
        unsupported: vec![],
        languages: BTreeMap::new(),
        git: read_git_info(root),
        skipped: vec![],
    };
    walk(root, root, &excludes, languages, &mut p);
    Ok(p)
}

fn walk(root: &Path, dir: &Path, excludes: &[Regex], wanted: &[String], p: &mut Project) {
    let rd = match std::fs::read_dir(dir) {
        Ok(rd) => rd,
        Err(e) => {
            p.skipped.push((to_repo_path(root, dir), format!("unreadable: {e}")));
            return;
        }
    };
    let mut entries: Vec<_> = rd.flatten().collect();
    entries.sort_by_key(|e| e.file_name()); // deterministic order
    for ent in entries {
        let abs = ent.path();
        let rel = to_repo_path(root, &abs);
        if excludes.iter().any(|r| r.is_match(&rel)) {
            continue;
        }
        let Ok(ft) = ent.file_type() else { continue };
        if ft.is_symlink() {
            p.skipped.push((rel, "symlink (not followed)".into()));
            continue;
        }
        let name = ent.file_name().to_string_lossy().into_owned();
        if ft.is_dir() {
            if !SKIP_DIRS.contains(&name.as_str()) {
                walk(root, &abs, excludes, wanted, p);
            }
            continue;
        }
        if !ft.is_file() {
            continue;
        }
        if p.files.len() + p.text_files.len() >= MAX_FILES {
            p.skipped.push((rel, format!("file limit {MAX_FILES} reached")));
            continue;
        }
        let size = ent.metadata().map(|m| m.len()).unwrap_or(0);
        let ext = abs.extension().and_then(|e| e.to_str()).unwrap_or("").to_ascii_lowercase();
        if DATA_EXTS.contains(&ext.as_str()) {
            p.data_files.push(abs.clone());
        }
        if size > MAX_FILE_BYTES {
            p.skipped.push((rel, format!("larger than {MAX_FILE_BYTES} bytes")));
            continue;
        }
        let declaration = name.ends_with(".d.ts") || name.ends_with(".d.mts") || name.ends_with(".d.cts");
        match Language::from_extension(&ext) {
            Some(_) if declaration || name.ends_with(".min.js") => {}
            Some(lang) => {
                *p.languages.entry(lang.name().to_owned()).or_default() += 1;
                if !lang.is_supported() {
                    p.unsupported.push((rel, lang.name().to_owned()));
                    p.text_files.push(abs);
                } else if wanted.iter().any(|w| w == lang.name()) {
                    p.files.push(SourceFile { path: rel, abs, language: lang, size });
                } else {
                    // Left out by the `languages` setting: an explicit, reported scope choice.
                    p.text_files.push(abs);
                }
            }
            None if TEXT_EXTS.contains(&ext.as_str()) || name.starts_with(".env") || is_runtime_pin_file(&name) => p.text_files.push(abs),
            None => {}
        }
    }
}

fn project_name(root: &Path) -> String {
    if let Ok(text) = std::fs::read_to_string(root.join("package.json"))
        && let Ok(v) = serde_json::from_str::<serde_json::Value>(&text)
        && let Some(n) = v.get("name").and_then(|n| n.as_str()).filter(|n| !n.is_empty() && n.len() < 200)
    {
        return n.to_owned();
    }
    root.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_else(|| "project".into())
}

fn is_sha(s: &str) -> bool {
    (40..=64).contains(&s.len()) && s.bytes().all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
}

/// Read HEAD without executing git.
pub fn read_git_info(root: &Path) -> Option<GitInfo> {
    let git = root.join(".git");
    if !std::fs::symlink_metadata(&git).map(|m| m.is_dir()).unwrap_or(false) {
        return None;
    }
    let head = std::fs::read_to_string(git.join("HEAD")).ok()?.trim().to_owned();
    if is_sha(&head) {
        return Some(GitInfo { commit: Some(head), branch: None });
    }
    let r = head.strip_prefix("ref: ")?;
    if !r.starts_with("refs/") || r.contains("..") || !r.chars().all(|c| c.is_ascii_alphanumeric() || "/._-".contains(c)) {
        return Some(GitInfo { commit: None, branch: None });
    }
    let branch = r.strip_prefix("refs/heads/").map(str::to_owned);
    if let Ok(sha) = std::fs::read_to_string(git.join(r)) {
        let sha = sha.trim();
        if is_sha(sha) {
            return Some(GitInfo { commit: Some(sha.to_owned()), branch });
        }
    }
    if let Ok(packed) = std::fs::read_to_string(git.join("packed-refs")) {
        for line in packed.lines() {
            if let Some((sha, name)) = line.split_once(' ')
                && name == r
                && is_sha(sha)
            {
                return Some(GitInfo { commit: Some(sha.to_owned()), branch });
            }
        }
    }
    Some(GitInfo { commit: None, branch })
}

/// Git invocation hardened against repository-local configuration that executes programs.
pub fn safe_git(root: &Path, args: &[&str]) -> Result<String> {
    let git = which("git").ok_or_else(|| Error::Environment("git is required for this command but was not found".into()))?;
    let mut argv: Vec<String> = vec![git.display().to_string()];
    for a in [
        "-c",
        "core.fsmonitor=false",
        "-c",
        "core.hooksPath=/dev/null",
        "-c",
        "diff.external=",
        "-c",
        "core.pager=cat",
        "-c",
        "protocol.allow=never",
        "--no-pager",
    ] {
        argv.push(a.into());
    }
    argv.extend(args.iter().map(|a| (*a).to_owned()));
    let mut o = RunOptions::new(root, Duration::from_secs(60));
    let mut env = crate::process::scrubbed_env(&[("GIT_CONFIG_NOSYSTEM", "1"), ("GIT_TERMINAL_PROMPT", "0")]);
    env.insert("GIT_CONFIG_GLOBAL".into(), "/dev/null".into());
    o.env = Some(env);
    let r = run(&argv, &o);
    if !r.success() {
        return Err(Error::Analysis(format!("git {} failed: {}", args.join(" "), r.stderr.trim())));
    }
    Ok(r.stdout)
}

/// Validate a user-supplied revision range (`base...head`).
pub fn validate_range(range: &str) -> Result<()> {
    static RE: std::sync::LazyLock<Regex> = std::sync::LazyLock::new(|| Regex::new(r"^[\w./@^~-]+(\.\.\.?[\w./@^~-]+)?$").expect("static regex"));
    if range.starts_with('-') || !RE.is_match(range) {
        return Err(Error::Usage(format!("invalid revision range: {range}")));
    }
    Ok(())
}

pub fn changed_files(root: &Path, range: &str) -> Result<Vec<String>> {
    validate_range(range)?;
    let out = safe_git(root, &["diff", "--name-only", "--no-ext-diff", "--no-textconv", range, "--"])?;
    Ok(out.lines().map(str::trim).filter(|l| !l.is_empty()).map(str::to_owned).collect())
}

pub fn diff_patch(root: &Path, range: &str) -> Result<String> {
    validate_range(range)?;
    safe_git(root, &["diff", "--no-ext-diff", "--no-textconv", range, "--"])
}

/// Content of `path` at revision `rev` (for policy-change detection).
pub fn file_at(root: &Path, rev: &str, path: &str) -> Option<String> {
    validate_range(rev).ok()?;
    if path.contains("..") || path.starts_with('/') {
        return None;
    }
    safe_git(root, &["show", &format!("{rev}:{path}")]).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn globs() {
        let r = glob_to_regex("src/**/*.test.ts").expect("re");
        assert!(r.is_match("src/a/b/x.test.ts"));
        assert!(!r.is_match("lib/x.test.ts"));
        assert!(glob_to_regex("fixtures").expect("re").is_match("fixtures/a/b.ts"));
    }

    #[test]
    fn symlinks_are_not_followed() {
        let d = tempfile::tempdir().expect("tmp");
        std::fs::write(d.path().join("a.ts"), "export const x = 1;").expect("w");
        std::os::unix::fs::symlink("/etc", d.path().join("etc")).expect("ln");
        let p = discover(d.path(), &[], &["typescript".into()]).expect("discover");
        assert_eq!(p.files.len(), 1);
        assert!(p.skipped.iter().any(|(f, why)| f == "etc" && why.contains("symlink")));
    }

    #[test]
    fn ranges_are_validated() {
        assert!(validate_range("origin/main...HEAD").is_ok());
        assert!(validate_range("--output=/tmp/x").is_err());
        assert!(validate_range("a;rm -rf /").is_err());
    }
}
