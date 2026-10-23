//! Configuration.
//!
//! Two sources with different trust:
//! - `.proof-it/config.yaml` lives in the analysed repository and is UNTRUSTED
//!   (an AI agent or attacker can edit it). Its schema has no field that names
//!   a program, a command or an absolute path; unknown keys are errors.
//! - The organisation policy (`--policy FILE`, `$PROOF_IT_POLICY`, or
//!   `~/.config/proof-it/policy.yaml`) lives outside the repository and is
//!   TRUSTED. It defines protected properties and the merge policy; the
//!   repository cannot weaken it (attempts are reported as policy violations).

use crate::error::{Error, Result};
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use std::sync::LazyLock;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum PolicyAction {
    Fail,
    Warn,
    Ignore,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields, default)]
pub struct Config {
    pub version: u32,
    pub project: ProjectSection,
    pub languages: Vec<String>,
    /// Extra excluded paths (globs with `*`/`**`), relative to the repository.
    pub exclude: Vec<String>,
    pub analysis: AnalysisSection,
    pub verification: VerificationSection,
    pub testing: TestingSection,
    pub properties: PropertiesSection,
    pub state_machines: Vec<StateMachineSpec>,
    pub authorization: AuthorizationSection,
    pub policy: PolicySection,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields, default)]
pub struct ProjectSection {
    pub name: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields, default)]
pub struct AnalysisSection {
    pub r#static: bool,
    pub security: bool,
    pub secrets: bool,
    pub dependencies: bool,
    pub formal: bool,
    pub fuzzing: bool,
    pub mutation: bool,
    pub external: ExternalSection,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields, default)]
pub struct ExternalSection {
    pub semgrep: bool,
    pub gitleaks: bool,
    pub osv: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields, default)]
pub struct VerificationSection {
    /// Seconds per Lean file.
    pub timeout: u64,
    pub parallel: bool,
    pub max_proofs: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields, default)]
pub struct TestingSection {
    /// Executing repository code (replay/attack) is opt-in.
    pub allow_execution: bool,
    pub iterations: usize,
    pub seed: Option<u64>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields, default)]
pub struct PropertiesSection {
    pub include: Vec<String>,
    pub exclude: Vec<String>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields, default)]
pub struct StateMachineSpec {
    /// Name of the state type (enum/union) or `entity.field` for inferred machines.
    pub r#type: String,
    pub initial: Option<String>,
    pub terminal: Vec<String>,
    pub forbidden: Vec<(String, String)>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields, default)]
pub struct AuthorizationSection {
    pub ownership_fields: Vec<String>,
    pub principal_paths: Vec<String>,
    pub admin_roles: Vec<String>,
    /// Project functions that enforce ownership (declared, not verified).
    pub guard_functions: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields, default)]
pub struct PolicySection {
    pub violated: PolicyAction,
    pub critical_security: PolicyAction,
    pub high_security: PolicyAction,
    pub unproven: PolicyAction,
    pub error: PolicyAction,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            version: 1,
            project: ProjectSection::default(),
            languages: vec!["typescript".into(), "javascript".into(), "go".into()],
            exclude: vec![],
            analysis: AnalysisSection::default(),
            verification: VerificationSection::default(),
            testing: TestingSection::default(),
            properties: PropertiesSection::default(),
            state_machines: vec![],
            authorization: AuthorizationSection::default(),
            policy: PolicySection::default(),
        }
    }
}
impl Default for AnalysisSection {
    fn default() -> Self {
        Self {
            r#static: true,
            security: true,
            secrets: true,
            dependencies: true,
            formal: true,
            fuzzing: true,
            mutation: false,
            external: ExternalSection::default(),
        }
    }
}
impl Default for ExternalSection {
    fn default() -> Self {
        Self { semgrep: true, gitleaks: true, osv: true }
    }
}
impl Default for VerificationSection {
    fn default() -> Self {
        Self { timeout: 120, parallel: true, max_proofs: 200 }
    }
}
impl Default for TestingSection {
    fn default() -> Self {
        Self { allow_execution: false, iterations: 500, seed: None }
    }
}
impl Default for AuthorizationSection {
    fn default() -> Self {
        let s = |xs: &[&str]| xs.iter().map(|x| (*x).to_owned()).collect();
        Self {
            ownership_fields: s(&["ownerId", "userId", "owner", "createdBy", "user_id", "owner_id"]),
            principal_paths: s(&["req.user.id", "req.user.sub", "req.auth.userId", "user.id", "principal.id", "ctx.user.id", "ctx.state.user.id"]),
            admin_roles: s(&["admin", "super_admin", "superadmin"]),
            guard_functions: vec![],
        }
    }
}
impl Default for PolicySection {
    fn default() -> Self {
        Self {
            violated: PolicyAction::Fail,
            critical_security: PolicyAction::Fail,
            high_security: PolicyAction::Warn,
            unproven: PolicyAction::Warn,
            error: PolicyAction::Warn,
        }
    }
}

pub const CONFIG_DIR: &str = ".proof-it";
pub const CONFIG_FILE: &str = "config.yaml";
const MAX_CONFIG_BYTES: u64 = 256 * 1024;

static IDENT: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"^[A-Za-z_$][\w$.]{0,100}$").expect("static regex"));
static GLOB: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"^[\w.\-*/@]{1,200}$").expect("static regex"));
static SELECTOR: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"^[\w.\-]{1,100}$").expect("static regex"));

fn read_limited(path: &Path) -> Result<String> {
    let meta = std::fs::metadata(path).map_err(|e| Error::io(path, e))?;
    if meta.len() > MAX_CONFIG_BYTES {
        return Err(Error::Config(format!("{} is larger than {MAX_CONFIG_BYTES} bytes", path.display())));
    }
    std::fs::read_to_string(path).map_err(|e| Error::io(path, e))
}

/// Parse YAML from an untrusted file with alias-expansion limits.
pub fn parse_yaml<T: serde::de::DeserializeOwned>(text: &str, source: &Path) -> Result<T> {
    let mut budget = serde_saphyr::Budget::default();
    budget.max_aliases = 50;
    let mut opts = serde_saphyr::Options::default();
    opts.budget = Some(budget);
    serde_saphyr::from_str_with_options(text, opts).map_err(|e| Error::Config(format!("{}: {e}", source.display())))
}

impl Config {
    pub fn validate(&self, source: &str) -> Result<()> {
        let mut errs: Vec<String> = Vec::new();
        if self.version != 1 {
            errs.push(format!("version: unsupported config version {} (expected 1)", self.version));
        }
        if self.project.name.len() > 200 {
            errs.push("project.name: too long".into());
        }
        for (i, g) in self.exclude.iter().enumerate() {
            if !GLOB.is_match(g) || g.starts_with('/') || g.contains("..") {
                errs.push(format!("exclude[{i}]: invalid glob {g:?}"));
            }
        }
        for (i, s) in self.properties.include.iter().chain(&self.properties.exclude).enumerate() {
            if !SELECTOR.is_match(s) {
                errs.push(format!("properties selector [{i}]: invalid value {s:?}"));
            }
        }
        for (i, sm) in self.state_machines.iter().enumerate() {
            if !IDENT.is_match(&sm.r#type) {
                errs.push(format!("state_machines[{i}].type: must be a type name"));
            }
        }
        let a = &self.authorization;
        for (k, list) in [
            ("ownership_fields", &a.ownership_fields),
            ("principal_paths", &a.principal_paths),
            ("guard_functions", &a.guard_functions),
            ("admin_roles", &a.admin_roles),
        ] {
            for v in list {
                if !IDENT.is_match(v) && k != "admin_roles" {
                    errs.push(format!("authorization.{k}: invalid value {v:?}"));
                }
            }
        }
        if !(1..=3600).contains(&self.verification.timeout) {
            errs.push("verification.timeout: expected 1..=3600 seconds".into());
        }
        if !(1..=1_000_000).contains(&self.testing.iterations) {
            errs.push("testing.iterations: expected 1..=1000000".into());
        }
        if errs.is_empty() { Ok(()) } else { Err(Error::Config(format!("invalid configuration in {source}:\n  - {}", errs.join("\n  - ")))) }
    }
}

#[derive(Debug, Clone)]
pub struct LoadedConfig {
    pub config: Config,
    pub path: Option<PathBuf>,
    /// Raw text, kept for policy-change detection.
    pub raw: Option<String>,
}

pub fn load_config(root: &Path) -> Result<LoadedConfig> {
    let path = root.join(CONFIG_DIR).join(CONFIG_FILE);
    match std::fs::symlink_metadata(&path) {
        Err(_) => {
            return Ok(LoadedConfig { config: Config::default(), path: None, raw: None });
        }
        Ok(m) if m.file_type().is_symlink() => {
            return Err(Error::Config(format!("{} is a symlink; refusing to follow it", path.display())));
        }
        Ok(_) => {}
    }
    let text = read_limited(&path)?;
    let config: Config = if text.trim().is_empty() { Config::default() } else { parse_yaml(&text, &path)? };
    config.validate(&path.display().to_string())?;
    Ok(LoadedConfig { config, path: Some(path), raw: Some(text) })
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct Suppression {
    /// Finding id, rule id or property id.
    pub finding: String,
    #[serde(default)]
    pub file: Option<String>,
    pub reason: String,
}

#[derive(Debug, Default, Deserialize)]
#[serde(deny_unknown_fields)]
struct SuppressionFile {
    #[serde(default)]
    suppressions: Vec<Suppression>,
}

pub fn load_suppressions(root: &Path) -> Result<Vec<Suppression>> {
    let path = root.join(CONFIG_DIR).join("suppressions.yaml");
    if !path.exists() {
        return Ok(vec![]);
    }
    let text = read_limited(&path)?;
    if text.trim().is_empty() {
        return Ok(vec![]);
    }
    let f: SuppressionFile = parse_yaml(&text, &path)?;
    let mut errs = Vec::new();
    for (i, s) in f.suppressions.iter().enumerate() {
        if s.finding.trim().is_empty() {
            errs.push(format!("suppressions[{i}].finding: required"));
        }
        // Every suppression must say why. Silent suppression is not allowed.
        if s.reason.trim().chars().count() < 10 {
            errs.push(format!("suppressions[{i}].reason: required (at least 10 characters)"));
        }
    }
    if errs.is_empty() { Ok(f.suppressions) } else { Err(Error::Config(format!("invalid {}:\n  - {}", path.display(), errs.join("\n  - ")))) }
}

/// Evidence requirements a change must meet, per risk tier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Requirement {
    /// Every affected property of this tier is PROVEN (non-vacuous, authoritative spec).
    FormalProof,
    /// No unsuppressed HIGH/CRITICAL security finding in the change.
    SecurityPass,
    /// Adversarial testing ran against the code and found no violation.
    AdversarialTest,
    /// No previously PROVEN property regressed.
    RegressionPass,
    /// No affected property of this tier is VIOLATED.
    NoViolation,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields, default)]
pub struct MergePolicy {
    pub critical: Vec<Requirement>,
    pub high: Vec<Requirement>,
    pub normal: Vec<Requirement>,
    /// Any change to verification policy (config, suppressions, properties) requires a human.
    pub policy_changes_require_human: bool,
}

impl Default for MergePolicy {
    fn default() -> Self {
        use Requirement::*;
        Self {
            critical: vec![FormalProof, SecurityPass, AdversarialTest, RegressionPass, NoViolation],
            high: vec![SecurityPass, RegressionPass, NoViolation],
            normal: vec![RegressionPass, NoViolation],
            policy_changes_require_human: true,
        }
    }
}

/// Trusted organisation policy. Never read from the analysed repository.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields, default)]
pub struct OrgPolicy {
    /// Properties the repository may not exclude, suppress or weaken.
    pub protected_properties: Vec<String>,
    pub merge_policy: MergePolicy,
    /// Organisation-wide state-machine specifications (override the repository's).
    pub state_machines: Vec<StateMachineSpec>,
    /// Roles that count as administrators for AUTHZ-002 (default: admin,
    /// super_admin, superadmin). Only this trusted file can add a role: the
    /// repository's `authorization.admin_roles` may only narrow the set.
    pub admin_roles: Option<Vec<String>>,
    /// Where this policy was loaded from (always overwritten by the loader).
    #[serde(default)]
    pub source: Option<String>,
}

/// The admin roles AUTHZ-002 proves against, and the repository's list when it
/// was ignored.
///
/// The repository configuration is untrusted: a role it adds would let an
/// agent or attacker "prove" that a non-admin role is an admin (configure
/// `user` as an admin role and every role check passes). The trusted set comes
/// from the organisation policy, else the built-in default; the repository may
/// narrow it (a smaller set only makes proofs harder) but never widen it.
pub fn effective_admin_roles(config: &Config, org: &OrgPolicy) -> (Vec<String>, Option<Vec<String>>) {
    let default = AuthorizationSection::default().admin_roles;
    let trusted = org.admin_roles.clone().unwrap_or_else(|| default.clone());
    let repo = &config.authorization.admin_roles;
    // Left at the default: the repository did not set it.
    if *repo == default {
        return (trusted, None);
    }
    if !repo.is_empty() && repo.iter().all(|r| trusted.contains(r)) { (repo.clone(), None) } else { (trusted, Some(repo.clone())) }
}

/// Load the organisation policy from (in order) an explicit path, `$PROOF_IT_POLICY`,
/// or `~/.config/proof-it/policy.yaml`. Refuses a policy file located inside `repo_root`.
pub fn load_org_policy(explicit: Option<&Path>, repo_root: &Path) -> Result<OrgPolicy> {
    let candidate = explicit
        .map(Path::to_path_buf)
        .or_else(|| std::env::var_os("PROOF_IT_POLICY").map(PathBuf::from))
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".config/proof-it/policy.yaml")).filter(|p| p.exists()));
    let Some(path) = candidate else {
        return Ok(OrgPolicy::default());
    };
    let canon = path.canonicalize().map_err(|e| Error::io(&path, e))?;
    if let Ok(root) = repo_root.canonicalize()
        && canon.starts_with(&root)
    {
        return Err(Error::Config(format!(
            "organisation policy {} lives inside the analysed repository; it must be outside the repository to be trusted",
            path.display()
        )));
    }
    let text = read_limited(&canon)?;
    let mut p: OrgPolicy = parse_yaml(&text, &canon)?;
    p.source = Some(canon.display().to_string());
    Ok(p)
}

pub fn init_template(name: &str) -> String {
    format!(
        r#"# Proof-It configuration. Every key is documented in docs/cli.md.
# This file is part of the repository and therefore UNTRUSTED input:
# changes to it are reported as verification-policy changes.
version: 1

project:
  name: {name:?}

languages: [typescript, javascript, go]

# Extra paths to skip (node_modules, dist, build, .git are always skipped).
exclude: []

analysis:
  static: true
  security: true
  secrets: true
  dependencies: true     # osv-scanner queries the OSV database over the network
  formal: true
  fuzzing: true
  mutation: false
  external:
    semgrep: true
    gitleaks: true
    osv: true

verification:
  timeout: 120           # seconds per Lean file
  parallel: true

testing:
  # Replaying counterexamples executes code from THIS repository in a sandbox.
  # Off by default; enable only for code you trust, or pass --allow-exec.
  allow_execution: false
  iterations: 500
  seed: null             # null = fixed default seed (runs are reproducible)

properties:
  include: []            # categories or ids; empty = all
  exclude: []

# Declare the intended lifecycle of state machines. Without this, terminal
# states are only INFERRED from their names and reported as such.
state_machines: []
#  - type: EmergencyStatus
#    initial: CREATED
#    terminal: [RESOLVED, CANCELLED]
#    forbidden:
#      - [RESOLVED, ACTIVE]

authorization:
  guard_functions: []    # e.g. [assertOwner, canAccess]

policy:
  violated: fail
  critical_security: fail
  high_security: warn
  unproven: warn
  error: warn
"#
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unknown_keys_are_rejected() {
        let r: Result<Config> = parse_yaml("version: 1\nanalysis:\n  formall: false\n", Path::new("c.yaml"));
        assert!(r.is_err());
    }

    #[test]
    fn defaults_validate() {
        assert!(Config::default().validate("default").is_ok());
    }

    #[test]
    fn traversal_globs_are_rejected() {
        let c = Config { exclude: vec!["../../etc".into()], ..Config::default() };
        assert!(c.validate("x").is_err());
    }

    #[test]
    fn template_parses() {
        let c: Config = parse_yaml(&init_template("demo"), Path::new("t")).expect("template must parse");
        assert!(c.validate("t").is_ok());
        assert!(!c.testing.allow_execution);
    }

    #[test]
    fn alias_bombs_are_limited() {
        let bomb = "a: &a [x,x,x,x,x,x,x,x,x]\nb: &b [*a,*a,*a,*a,*a,*a,*a,*a,*a]\nc: &c [*b,*b,*b,*b,*b,*b,*b,*b,*b]\nd: &d [*c,*c,*c,*c,*c,*c,*c,*c,*c]\ne: [*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d,*d]\n";
        let r: Result<serde_json::Value> = parse_yaml(bomb, Path::new("bomb"));
        assert!(r.is_err());
    }

    #[test]
    fn org_policy_round_trips() {
        let p = OrgPolicy { protected_properties: vec!["AUTHZ-001".into()], source: Some("/etc/x".into()), ..OrgPolicy::default() };
        let back: OrgPolicy = serde_json::from_str(&serde_json::to_string(&p).expect("ser")).expect("de");
        assert_eq!(back, p);
    }

    #[test]
    fn suppressions_need_reasons() {
        let dir = tempfile::tempdir().expect("tmp");
        std::fs::create_dir(dir.path().join(".proof-it")).expect("mkdir");
        std::fs::write(dir.path().join(".proof-it/suppressions.yaml"), "suppressions:\n  - finding: SEC-SQLI\n    reason: ok\n").expect("write");
        assert!(load_suppressions(dir.path()).is_err());
    }
}

#[cfg(test)]
mod admin_role_trust {
    use super::*;

    fn cfg(roles: &[&str]) -> Config {
        let mut c = Config::default();
        c.authorization.admin_roles = roles.iter().map(|r| (*r).to_owned()).collect();
        c
    }
    fn org(roles: Option<&[&str]>) -> OrgPolicy {
        OrgPolicy { admin_roles: roles.map(|r| r.iter().map(|x| (*x).to_owned()).collect()), ..OrgPolicy::default() }
    }
    fn set(v: &[&str]) -> Vec<String> {
        v.iter().map(|x| (*x).to_owned()).collect()
    }

    #[test]
    fn repository_cannot_add_admin_roles() {
        // An agent declaring every role an admin: ignored, reported.
        let (roles, ignored) = effective_admin_roles(&cfg(&["admin", "user"]), &org(None));
        assert_eq!(roles, set(&["admin", "super_admin", "superadmin"]));
        assert_eq!(ignored, Some(set(&["admin", "user"])));
        // Even a role the organisation might accept, unless the organisation says so.
        let (roles, ignored) = effective_admin_roles(&cfg(&["admin", "organization_admin"]), &org(None));
        assert!(!roles.contains(&"organization_admin".to_owned()));
        assert!(ignored.is_some());
        // An empty list would make every admin check vacuous.
        assert!(effective_admin_roles(&cfg(&[]), &org(None)).1.is_some());
    }

    #[test]
    fn repository_may_narrow_and_organisation_decides() {
        assert_eq!(effective_admin_roles(&cfg(&["super_admin"]), &org(None)), (set(&["super_admin"]), None));
        let o = org(Some(&["admin", "super_admin", "organization_admin"]));
        // Repository left at the default: the organisation's set applies, no warning.
        assert_eq!(effective_admin_roles(&Config::default(), &o), (set(&["admin", "super_admin", "organization_admin"]), None));
        // The organisation's set can be narrowed by the repository, not widened.
        assert_eq!(effective_admin_roles(&cfg(&["organization_admin"]), &o), (set(&["organization_admin"]), None));
        assert!(effective_admin_roles(&cfg(&["organization_admin", "user"]), &o).1.is_some());
    }
}
