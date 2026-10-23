//! INFRA-003: the Node.js runtime a project runs on is a supported, patched
//! release.
//!
//! Lockfile scanners never see the runtime, so a service built on an
//! end-of-life `node:18` image, or on a Node.js older than the latest security
//! release, passes the dependency check untouched. This check reads every
//! place a project pins Node.js (container images, version files,
//! `package.json`, CI) and compares each pin with the embedded table in
//! `data/node-runtime-advisories.yaml`.
//!
//! It reports what the pins say, not what is deployed: a floating tag such as
//! `node:22-alpine` is only as patched as the last rebuild, so it is reported
//! with low severity and the exact version to pin.

use proof_it_core::paths::to_repo_path;
use proof_it_core::types::*;
use regex::Regex;
use serde::Deserialize;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::LazyLock;

/// Rule ids produced by this check.
pub const RULE_IDS: &[&str] = &["node-runtime:eol", "node-runtime:unpatched", "node-runtime:floating", "node-runtime:engines-eol"];

const PROPERTY: &str = "INFRA-003";
const DATA: &str = include_str!("../../../data/node-runtime-advisories.yaml");

#[derive(Debug, Deserialize)]
struct Table {
    updated: String,
    supported: Vec<u32>,
    releases: Vec<Release>,
}

#[derive(Debug, Deserialize)]
struct Release {
    id: String,
    date: String,
    severity: String,
    url: String,
    summary: String,
    cves: Vec<String>,
    fixed: BTreeMap<String, String>,
}

#[allow(clippy::expect_used)]
static TABLE: LazyLock<Table> = LazyLock::new(|| serde_saphyr::from_str(DATA).expect("embedded node-runtime-advisories.yaml is valid"));

#[allow(clippy::expect_used)]
fn re(s: &str) -> Regex {
    Regex::new(s).expect("static regex")
}

// `FROM [--platform=…] [registry/…/]node:<tag>` and compose `image: …node:<tag>`.
static IMAGE: LazyLock<Regex> = LazyLock::new(|| re(r"(?mi)^\s*(?:FROM(?:\s+--\S+)*|-?\s*image:)\s+['\x22]?(?:[\w.\-]+(?::\d+)?/)*node:([\w.\-]+)"));
static NODE_VERSION_KEY: LazyLock<Regex> = LazyLock::new(|| re(r"(?m)^\s*-?\s*node-version:\s*(.+?)\s*$"));
static TOOL_VERSIONS: LazyLock<Regex> = LazyLock::new(|| re(r"(?m)^\s*(?:nodejs|node)\s+(\S+)"));
static VERSION: LazyLock<Regex> = LazyLock::new(|| re(r"^v?(\d+)(?:\.(\d+|x))?(?:\.(\d+|x))?(?:$|[-+_])"));

/// A Node.js version as written in a pin. `minor`/`patch` are `None` when the
/// pin floats (`22`, `22.x`, `node:22-alpine`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Pin {
    major: u32,
    minor: Option<u32>,
    patch: Option<u32>,
}

impl Pin {
    fn exact(&self) -> Option<(u32, u32, u32)> {
        Some((self.major, self.minor?, self.patch?))
    }
}

fn codename(s: &str) -> Option<u32> {
    Some(match s.to_ascii_lowercase().as_str() {
        "argon" => 4,
        "boron" => 6,
        "carbon" => 8,
        "dubnium" => 10,
        "erbium" => 12,
        "fermium" => 14,
        "gallium" => 16,
        "hydrogen" => 18,
        "iron" => 20,
        "jod" => 22,
        "krypton" => 24,
        _ => return None,
    })
}

/// Parses `18`, `v18.20.4`, `22.x`, `22.23.4-alpine3.20`, `lts/hydrogen`,
/// `18-bookworm-slim`. Floating names with no line (`lts`, `latest`,
/// `current`, `alpine`) return `None`: they cannot be judged from the file.
fn parse_pin(raw: &str) -> Option<Pin> {
    let s = raw.trim().trim_matches(|c| c == '\'' || c == '"');
    if let Some(name) = s.strip_prefix("lts/") {
        return codename(name).map(|major| Pin { major, minor: None, patch: None });
    }
    let c = VERSION.captures(s)?;
    let num = |i: usize| c.get(i).and_then(|m| m.as_str().parse::<u32>().ok());
    Some(Pin { major: num(1)?, minor: num(2), patch: num(2).and(num(3)) })
}

fn parse_triple(s: &str) -> Option<(u32, u32, u32)> {
    let mut it = s.trim().split('.').map(|p| p.parse::<u32>().ok());
    Some((it.next()??, it.next()??, it.next()??))
}

fn newest_supported() -> u32 {
    TABLE.supported.iter().copied().max().unwrap_or(0)
}

/// End of life: not supported, and not a line newer than the table knows.
fn is_eol(major: u32) -> bool {
    !TABLE.supported.contains(&major) && major <= newest_supported()
}

fn severity(s: &str) -> Severity {
    match s {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "low" => Severity::Low,
        _ => Severity::Medium,
    }
}

/// Security releases on `major` whose fix the pin predates.
fn missed(pin: &Pin) -> Vec<(&'static Release, String)> {
    let Some(have) = pin.exact() else { return vec![] };
    TABLE
        .releases
        .iter()
        .filter_map(|r| {
            let fixed = r.fixed.get(&pin.major.to_string())?;
            (have < parse_triple(fixed)?).then(|| (r, fixed.clone()))
        })
        .collect()
}

fn line_of(text: &str, offset: usize) -> u32 {
    u32::try_from(text[..offset].matches('\n').count() + 1).unwrap_or(u32::MAX)
}

#[allow(clippy::too_many_arguments)]
fn finding(rule: &str, sev: Severity, file: &str, line: u32, snippet: &str, title: String, desc: String, rec: String) -> Finding {
    let location = SourceLocation { file: file.into(), line, column: None, end_line: None, snippet: Some(snippet.trim().chars().take(160).collect()) };
    Finding {
        id: fingerprint(rule, Some(&location), ""),
        rule_id: rule.into(),
        property_id: Some(PROPERTY.into()),
        title,
        source: FindingSource::Dependencies,
        severity: sev,
        confidence: Confidence::High,
        evidence: vec![Evidence::new(
            EvidenceKind::StaticPattern,
            format!("{} (advisory table updated {})", location.snippet.clone().unwrap_or_default(), TABLE.updated),
        )],
        location: Some(location),
        description: desc,
        recommendation: Some(rec),
        cwe: vec!["CWE-1104".into()],
        suppressed: None,
        baseline: None,
    }
}

fn recommended() -> String {
    let mut fixes: Vec<String> = TABLE.supported.iter().filter_map(|m| latest_fix(*m).map(|v| format!("{v}+"))).collect();
    if fixes.is_empty() {
        fixes = TABLE.supported.iter().map(|m| format!("{m}.x")).collect();
    }
    fixes.join(" or ")
}

fn latest_fix(major: u32) -> Option<String> {
    TABLE.releases.iter().filter_map(|r| r.fixed.get(&major.to_string())).max_by_key(|v| parse_triple(v)).cloned()
}

/// Judges one pin. `what` names the pin for the message ("container image
/// node:18-alpine", ".nvmrc 18").
fn judge(pin: Pin, what: &str, file: &str, line: u32, snippet: &str, out: &mut Vec<Finding>) {
    if is_eol(pin.major) {
        let since: Vec<String> = TABLE.releases.iter().map(|r| format!("{} ({})", r.id, r.cves.len())).collect();
        out.push(finding(
            "node-runtime:eol",
            Severity::High,
            file,
            line,
            snippet,
            format!("End-of-life Node.js {} ({what})", pin.major),
            format!(
                "{what} runs Node.js {}, which no longer receives security fixes. End-of-life lines are affected by every \
                 later security release and will never be patched{}.",
                pin.major,
                if since.is_empty() { String::new() } else { format!("; known releases since: {}", since.join(", ")) }
            ),
            format!("Move to a supported, patched release: {}.", recommended()),
        ));
        return;
    }
    if !TABLE.supported.contains(&pin.major) {
        return; // newer than the table: nothing known against it
    }
    let missed = missed(&pin);
    if let Some(worst) = missed.iter().map(|(r, _)| severity(&r.severity)).max() {
        let (newest, fix) = missed.iter().max_by_key(|(r, _)| r.date.clone()).map(|(r, f)| (*r, f.clone())).unwrap_or((missed[0].0, missed[0].1.clone()));
        let cves: Vec<&str> = missed.iter().flat_map(|(r, _)| r.cves.iter().map(String::as_str)).collect();
        let (maj, min, pat) = pin.exact().unwrap_or((pin.major, 0, 0));
        out.push(finding(
            "node-runtime:unpatched",
            worst,
            file,
            line,
            snippet,
            format!("Node.js {maj}.{min}.{pat} predates the {} security release ({what})", newest.id),
            format!("{what} pins Node.js {maj}.{min}.{pat}. {} ({}). Affected: {}.", newest.summary.trim(), newest.url, cves.join(", ")),
            format!("Pin Node.js {fix} or later on this line, rebuild, and redeploy."),
        ));
        return;
    }
    if pin.exact().is_none()
        && let Some(fix) = latest_fix(pin.major)
    {
        out.push(finding(
            "node-runtime:floating",
            Severity::Low,
            file,
            line,
            snippet,
            format!("Floating Node.js {} pin ({what})", pin.major),
            format!(
                "{what} floats on the Node.js {} line, so the version that ships is whatever was current at the last \
                     build. It contains the {} fixes only if it was rebuilt after {}.",
                pin.major,
                TABLE.releases.iter().filter(|r| r.fixed.contains_key(&pin.major.to_string())).map(|r| r.id.as_str()).collect::<Vec<_>>().join(", "),
                TABLE.releases.iter().map(|r| r.date.as_str()).max().unwrap_or("-")
            ),
            format!("Pin the exact patched version ({fix} or later) so a build cannot pick up an older one."),
        ));
    }
}

/// The lowest major an `engines.node` range admits (`>=18`, `^18.17`, `18.x || 20.x`).
fn engines_floor(range: &str) -> Option<u32> {
    static NUM: LazyLock<Regex> = LazyLock::new(|| re(r"(?:^|[\s|,(])(?:>=|\^|~|=|v)?\s*(\d+)"));
    let mut floors: Vec<u32> = Vec::new();
    for alt in range.split("||") {
        let alt = alt.trim();
        if alt.starts_with('<') {
            floors.push(0);
            continue;
        }
        if let Some(c) = NUM.captures(&format!(" {alt}"))
            && let Ok(m) = c[1].parse()
        {
            floors.push(m);
        }
    }
    floors.into_iter().min()
}

fn json_key_line(text: &str, key: &str) -> u32 {
    text.find(&format!("\"{key}\"")).map_or(1, |o| line_of(text, o))
}

/// Scans the project's text files for Node.js runtime pins.
pub fn scan(root: &Path, files: &[PathBuf]) -> Vec<Finding> {
    let mut out = Vec::new();
    for abs in files {
        let Ok(text) = std::fs::read_to_string(abs) else { continue };
        let file = to_repo_path(root, abs);
        let name = abs.file_name().and_then(|n| n.to_str()).unwrap_or("");
        let lower = name.to_ascii_lowercase();
        let is_dockerfile = lower == "dockerfile" || lower.starts_with("dockerfile.") || lower.ends_with(".dockerfile") || lower == "containerfile";
        let is_yaml = lower.ends_with(".yml") || lower.ends_with(".yaml");

        if is_dockerfile || (is_yaml && (lower.contains("compose") || text.contains("image:"))) {
            for c in IMAGE.captures_iter(&text) {
                let (Some(all), Some(tag)) = (c.get(0), c.get(1)) else { continue };
                if let Some(pin) = parse_pin(tag.as_str()) {
                    judge(pin, &format!("container image node:{}", tag.as_str()), &file, line_of(&text, all.start()), all.as_str(), &mut out);
                }
            }
        }
        if is_yaml && file.contains(".github/workflows/") {
            for c in NODE_VERSION_KEY.captures_iter(&text) {
                let (Some(all), Some(val)) = (c.get(0), c.get(1)) else { continue };
                let v = val.as_str().trim();
                if v.contains("${{") {
                    continue; // matrix reference: the values are judged where the matrix lists them
                }
                let items: Vec<&str> = v.trim_start_matches('[').trim_end_matches(']').split(',').map(str::trim).filter(|s| !s.is_empty()).collect();
                for item in items {
                    if let Some(pin) = parse_pin(item) {
                        judge(
                            pin,
                            &format!("CI node-version {}", item.trim_matches(|c| c == '\'' || c == '"')),
                            &file,
                            line_of(&text, all.start()),
                            all.as_str(),
                            &mut out,
                        );
                    }
                }
            }
        }
        if (lower == ".nvmrc" || lower == ".node-version")
            && let Some(first) = text.lines().map(str::trim).find(|l| !l.is_empty() && !l.starts_with('#'))
            && let Some(pin) = parse_pin(first)
        {
            judge(pin, &format!("{name} {first}"), &file, 1, first, &mut out);
        }
        if lower == ".tool-versions" {
            for c in TOOL_VERSIONS.captures_iter(&text) {
                let (Some(all), Some(v)) = (c.get(0), c.get(1)) else { continue };
                if let Some(pin) = parse_pin(v.as_str()) {
                    judge(pin, &format!(".tool-versions {}", v.as_str()), &file, line_of(&text, all.start()), all.as_str(), &mut out);
                }
            }
        }
        if lower == "package.json" && !file.contains("node_modules/") {
            let Ok(pkg) = serde_json::from_str::<serde_json::Value>(&text) else { continue };
            if let Some(v) = pkg["volta"]["node"].as_str()
                && let Some(pin) = parse_pin(v)
            {
                judge(pin, &format!("volta.node {v}"), &file, json_key_line(&text, "volta"), v, &mut out);
            }
            if let Some(range) = pkg["engines"]["node"].as_str()
                && let Some(floor) = engines_floor(range).filter(|m| is_eol(*m))
            {
                out.push(finding(
                    "node-runtime:engines-eol",
                    Severity::Medium,
                    &file,
                    json_key_line(&text, "engines"),
                    &format!("\"node\": \"{range}\""),
                    format!("engines.node \"{range}\" admits end-of-life Node.js {floor}"),
                    format!(
                        "package.json declares Node.js \"{range}\", which accepts Node.js {floor}. That line no longer \
                             receives security fixes, so installs and platforms that honour engines can run it."
                    ),
                    format!("Raise the minimum to a patched supported release: {}.", recommended()),
                ));
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(files: &[(&str, &str)]) -> Vec<Finding> {
        let d = tempfile::tempdir().expect("tmp");
        let mut paths = Vec::new();
        for (rel, body) in files {
            let p = d.path().join(rel);
            std::fs::create_dir_all(p.parent().expect("parent")).expect("mkdir");
            std::fs::write(&p, body).expect("write");
            paths.push(p);
        }
        scan(d.path(), &paths)
    }

    fn rules(f: &[Finding]) -> Vec<&str> {
        f.iter().map(|x| x.rule_id.as_str()).collect()
    }

    #[test]
    fn table_is_valid_and_consistent() {
        assert!(!TABLE.supported.is_empty());
        for r in &TABLE.releases {
            assert!(!r.cves.is_empty(), "{} lists no CVEs", r.id);
            for (line, v) in &r.fixed {
                let (maj, _, _) = parse_triple(v).unwrap_or_else(|| panic!("{}: bad version {v}", r.id));
                assert_eq!(line, &maj.to_string(), "{}: {v} filed under line {line}", r.id);
            }
        }
    }

    #[test]
    fn parses_pins() {
        assert_eq!(parse_pin("18"), Some(Pin { major: 18, minor: None, patch: None }));
        assert_eq!(parse_pin("v18.20.4"), Some(Pin { major: 18, minor: Some(20), patch: Some(4) }));
        assert_eq!(parse_pin("22.23.4-alpine3.20"), Some(Pin { major: 22, minor: Some(23), patch: Some(4) }));
        assert_eq!(parse_pin("'22.x'"), Some(Pin { major: 22, minor: None, patch: None }));
        assert_eq!(parse_pin("18-bookworm-slim").map(|p| p.major), Some(18));
        assert_eq!(parse_pin("lts/hydrogen").map(|p| p.major), Some(18));
        assert_eq!(parse_pin("lts-alpine"), None);
        assert_eq!(parse_pin("latest"), None);
    }

    #[test]
    fn end_of_life_image_is_high() {
        let f = run(&[("api/Dockerfile", "FROM node:18-alpine AS build\nRUN npm ci\nFROM node:18-alpine\n")]);
        assert_eq!(rules(&f), ["node-runtime:eol", "node-runtime:eol"]);
        assert_eq!(f[0].severity, Severity::High);
        assert_eq!(f[1].location.as_ref().map(|l| l.line), Some(3));
        assert_eq!(f[0].property_id.as_deref(), Some("INFRA-003"));
    }

    #[test]
    fn unpatched_exact_version_lists_the_release() {
        let f = run(&[("Dockerfile", "FROM --platform=$BUILDPLATFORM docker.io/library/node:22.20.0-alpine\n")]);
        assert_eq!(rules(&f), ["node-runtime:unpatched"]);
        assert_eq!(f[0].severity, Severity::High);
        assert!(f[0].description.contains("CVE-2026-111497"), "{}", f[0].description);
        assert!(f[0].recommendation.as_deref().unwrap_or("").contains("22.23.4"));
    }

    #[test]
    fn patched_versions_are_clean() {
        let f = run(&[
            ("Dockerfile", "FROM node:22.23.4-alpine\n"),
            ("b/Dockerfile.prod", "FROM node:24.22.1\n"),
            (".nvmrc", "26.12.1\n"),
            (".github/workflows/ci.yml", "      - uses: actions/setup-node@v4\n        with:\n          node-version: '22.23.4'\n"),
        ]);
        assert!(f.is_empty(), "{f:#?}");
    }

    #[test]
    fn floating_supported_tag_is_low() {
        let f = run(&[("Dockerfile", "FROM node:22-alpine\n")]);
        assert_eq!(rules(&f), ["node-runtime:floating"]);
        assert_eq!(f[0].severity, Severity::Low);
        assert!(f[0].recommendation.as_deref().unwrap_or("").contains("22.23.4"));
    }

    #[test]
    fn ci_version_files_compose_and_engines() {
        let f = run(&[
            (
                ".github/workflows/deploy.yml",
                "        with:\n          node-version: \"18\"\n      matrix:\n        node-version: [20.x, 22.23.4]\n          node-version: ${{ matrix.node-version }}\n",
            ),
            (".node-version", "v20.11.1\n"),
            (".tool-versions", "nodejs 18.20.4\npython 3.12\n"),
            ("docker-compose.yml", "services:\n  web:\n    image: node:16\n"),
            ("svc/package.json", "{\n  \"name\": \"x\",\n  \"engines\": { \"node\": \">=18.0.0\" }\n}\n"),
            ("ok/package.json", "{ \"engines\": { \"node\": \">=22.23.4\" } }"),
        ]);
        let mut got = rules(&f);
        got.sort_unstable();
        assert_eq!(
            got,
            ["node-runtime:engines-eol", "node-runtime:eol", "node-runtime:eol", "node-runtime:eol", "node-runtime:eol", "node-runtime:eol"],
            "{f:#?}"
        );
    }

    #[test]
    fn engines_floor_reads_ranges() {
        assert_eq!(engines_floor(">=18.0.0"), Some(18));
        assert_eq!(engines_floor("^20.10 || ^22.11"), Some(20));
        assert_eq!(engines_floor("18.x"), Some(18));
        assert_eq!(engines_floor("<23"), Some(0));
        assert_eq!(engines_floor(">=22.23.4"), Some(22));
    }

    #[test]
    fn unknown_or_future_lines_are_not_flagged() {
        let f = run(&[("Dockerfile", "FROM node:lts-alpine\nFROM node:latest\nFROM node:30.1.0\nFROM nodejs:18\n")]);
        assert!(f.is_empty(), "{f:#?}");
    }
}
