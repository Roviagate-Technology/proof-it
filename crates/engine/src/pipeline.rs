//! The orchestrator: discovery → parsing/facts → analyses → formal → attack →
//! self-tests → change assessment → verdict → evidence.

use crate::change::{self, ChangeAssessment};
use crate::exec::Executor;
use crate::selftest::{self, MutationReport};
use crate::verdict::{self, AssuranceLevel, ProofDebt, Verdict};
use crate::{attack, external, secrets};
use proof_it_core::config::{Config, OrgPolicy, Suppression, load_config, load_org_policy, load_suppressions, parse_yaml};
use proof_it_core::facts::ProgramFacts;
use proof_it_core::process::sandbox_available;
use proof_it_core::project::{self, Project};
use proof_it_core::property::{Property, Registry};
use proof_it_core::rng::DEFAULT_SEED;
use proof_it_core::store::{ProofCache, RunStore, evidence_base, timestamp};
use proof_it_core::types::*;
use proof_it_core::{Error, Result};
use proof_it_model::extract::ExtractContext;
use proof_it_model::formal::{FormalOptions, key, run as run_formal};
use proof_it_model::lean::runner::toolchain;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant, SystemTime};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Stage {
    Static,
    Security,
    Secrets,
    Dependencies,
    External,
    Formal,
    Attack,
    Selfcheck,
    Mutation,
}

#[derive(Debug, Clone)]
pub struct Options {
    pub path: PathBuf,
    pub command: String,
    pub stages: BTreeSet<Stage>,
    pub seed: Option<u64>,
    pub safe: bool,
    pub allow_exec: bool,
    pub quick: bool,
    pub deep: bool,
    pub offline: bool,
    pub properties: Vec<String>,
    pub diff: Option<String>,
    pub baseline: Option<String>,
    pub out_dir: Option<PathBuf>,
    pub no_cache: bool,
    pub timeout: Option<u64>,
    pub policy: Option<PathBuf>,
    pub agent: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProjectInfo {
    pub root: String,
    pub name: String,
    pub commit: Option<String>,
    pub branch: Option<String>,
    pub languages: BTreeMap<String, usize>,
    pub files: usize,
    pub functions: usize,
    pub parse_errors: Vec<(String, String)>,
    pub skipped: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Environment {
    pub proof_it: String,
    pub lean: Option<String>,
    pub sandbox: bool,
    pub platform: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PropertyInfo {
    pub id: String,
    pub name: String,
    pub category: String,
    pub severity: Severity,
    pub version: u32,
    pub source: SpecSource,
    pub formal: bool,
    pub protected: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AttackSummary {
    pub replays: usize,
    pub reproduced: usize,
    pub cases: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Report {
    pub format: String,
    pub run_id: String,
    pub run_dir: String,
    pub command: String,
    pub started_at: String,
    pub duration_ms: u64,
    pub project: ProjectInfo,
    pub environment: Environment,
    pub seed: u64,
    pub options: BTreeMap<String, serde_json::Value>,
    pub config: Config,
    pub config_path: Option<String>,
    pub org_policy: OrgPolicy,
    pub stages: Vec<StageRun>,
    pub properties: Vec<PropertyInfo>,
    pub results: Vec<PropertyResult>,
    pub findings: Vec<Finding>,
    pub suppressions: Vec<Suppression>,
    pub attack: Option<AttackSummary>,
    pub mutation: Option<MutationReport>,
    pub change: Option<ChangeAssessment>,
    pub verdict: Verdict,
    pub assurance_level: AssuranceLevel,
    pub proof_debt: ProofDebt,
    pub max_formalization_level: u8,
}

pub const REPORT_FORMAT: &str = "proof-it/report@1";

fn ms(i: Instant) -> u64 {
    u64::try_from(i.elapsed().as_millis()).unwrap_or(u64::MAX)
}

/// Parse every file into facts (in parallel) and collect language-specific findings.
pub fn analyze_files(project: &Project) -> (ProgramFacts, Vec<Finding>) {
    let known: HashSet<String> = project.files.iter().map(|f| f.path.clone()).collect();
    let workers = std::thread::available_parallelism().map_or(4, |n| n.get()).clamp(1, 16);
    let chunks: Vec<&[proof_it_core::project::SourceFile]> = project.files.chunks(project.files.len().div_ceil(workers).max(1)).collect();
    let mut facts = ProgramFacts::default();
    let mut findings = Vec::new();
    std::thread::scope(|s| {
        let handles: Vec<_> = chunks
            .iter()
            .map(|chunk| {
                let known = &known;
                s.spawn(move || {
                    let mut out = Vec::new();
                    for f in *chunk {
                        let res = std::fs::read_to_string(&f.abs).map_err(|e| e.to_string()).and_then(|text| {
                            std::panic::catch_unwind(|| match f.language {
                                proof_it_core::facts::Language::Go => proof_it_lang_go::analyze(&f.path, &text),
                                _ => proof_it_lang_ts::analyze(&f.path, &text, known),
                            })
                            .unwrap_or_else(|_| Err("adapter panicked on this file".into()))
                        });
                        out.push((f.path.clone(), res));
                    }
                    out
                })
            })
            .collect();
        for h in handles {
            for (path, res) in h.join().unwrap_or_default() {
                match res {
                    Ok(a) => {
                        findings.extend(a.findings);
                        facts.texts.push((path, a.text));
                        facts.modules.push(a.facts);
                    }
                    Err(e) => facts.parse_errors.push((path, e)),
                }
            }
        }
    });
    facts.modules.sort_by(|a, b| a.file.cmp(&b.file));
    facts.texts.sort();
    (facts, findings)
}

fn apply_suppressions(findings: &mut [Finding], results: &mut [PropertyResult], sups: &[Suppression], org: &OrgPolicy) {
    let protected = |id: &str| org.protected_properties.iter().any(|p| p.eq_ignore_ascii_case(id));
    for f in findings.iter_mut() {
        if let Some(s) = sups.iter().find(|s| {
            (s.finding == f.id || s.finding == f.rule_id || f.property_id.as_deref() == Some(s.finding.as_str()))
                && s.file.as_ref().is_none_or(|x| f.location.as_ref().is_some_and(|l| &l.file == x))
        }) {
            // Findings on protected properties cannot be suppressed from the repository.
            if !f.property_id.as_deref().is_some_and(protected) {
                f.suppressed = Some(s.reason.clone());
            }
        }
    }
    for r in results.iter_mut() {
        if !matches!(r.status(), ProofStatus::Violated | ProofStatus::Unproven) || protected(&r.property_id) {
            continue;
        }
        if let Some(s) = sups.iter().find(|s| {
            s.finding.eq_ignore_ascii_case(&r.property_id)
                && s.file.as_ref().is_none_or(|x| r.location.as_ref().is_some_and(|l| &l.file == x) || r.target.contains(x.as_str()))
        }) {
            r.suppressed = Some(s.reason.clone());
            r.evidence.push(Evidence::new(EvidenceKind::Assumption, format!("suppressed: {}", s.reason)));
        }
    }
}

pub fn run(opts: &Options) -> Result<Report> {
    let started = Instant::now();
    let started_at = timestamp(SystemTime::now());
    let root = opts.path.canonicalize().map_err(|e| Error::Usage(format!("{}: {e}", opts.path.display())))?;
    let loaded = load_config(&root)?;
    let mut config = loaded.config.clone();
    if let Some(t) = opts.timeout {
        config.verification.timeout = t;
    }
    let suppressions = load_suppressions(&root)?;
    let org = load_org_policy(opts.policy.as_deref(), &root)?;
    let seed = opts.seed.or(config.testing.seed).unwrap_or(DEFAULT_SEED);
    let base = evidence_base(&root, opts.out_dir.as_deref())?;
    let store = RunStore::create(&base)?;
    let registry = Registry::load(Some(&root))?;
    let include = if opts.properties.is_empty() { config.properties.include.clone() } else { opts.properties.clone() };
    // Protected properties cannot be excluded by the repository.
    let exclude: Vec<String> =
        config.properties.exclude.iter().filter(|x| !org.protected_properties.iter().any(|p| p.eq_ignore_ascii_case(x))).cloned().collect();
    let props: Vec<&Property> = registry.select(&include, &exclude);
    if !opts.properties.is_empty() && props.is_empty() {
        return Err(Error::Usage(format!("no property matches {}; see `proof-it properties`", opts.properties.join(", "))));
    }

    let mut stages = Vec::new();
    let t = Instant::now();
    let project = project::discover(&root, &config.exclude, &config.languages)?;
    let (facts, adapter_findings) = analyze_files(&project);
    stages.push(StageRun::new(
        "parse",
        StageStatus::Ran,
        ms(t),
        format!("{} file(s), {} function(s), {} parse error(s)", facts.modules.len(), facts.function_count(), facts.parse_errors.len()),
    ));
    let mut findings: Vec<Finding> = Vec::new();
    for (stage, src, enabled) in
        [(Stage::Static, FindingSource::Static, config.analysis.r#static), (Stage::Security, FindingSource::Security, config.analysis.security)]
    {
        if opts.stages.contains(&stage) && enabled {
            let fs: Vec<Finding> = adapter_findings.iter().filter(|f| f.source == src).cloned().collect();
            stages.push(StageRun::new(if stage == Stage::Static { "static" } else { "security" }, StageStatus::Ran, 0, format!("{} finding(s)", fs.len())));
            findings.extend(fs);
        }
    }
    if opts.stages.contains(&Stage::Security) && config.analysis.security {
        let t = Instant::now();
        let mut fs = crate::appchecks::templates(&root, &project.text_files);
        fs.extend(crate::appchecks::app_config(&root, &facts));
        stages.push(StageRun::new("app-config", StageStatus::Ran, ms(t), format!("{} finding(s)", fs.len())));
        findings.extend(fs);
    }
    if opts.stages.contains(&Stage::Secrets) && config.analysis.secrets {
        let t = Instant::now();
        let files: Vec<PathBuf> = project.files.iter().map(|f| f.abs.clone()).chain(project.text_files.iter().cloned()).collect();
        let mut fs = secrets::scan(&root, &files);
        fs.extend(crate::datafiles::scan(&root, &project.data_files));
        stages.push(StageRun::new("secrets", StageStatus::Ran, ms(t), format!("{} finding(s)", fs.len())));
        findings.extend(fs);
    }
    if opts.stages.contains(&Stage::External) {
        let timeout = Duration::from_secs(if opts.deep { 900 } else { 300 });
        let (do_sg, do_gl, do_osv) = (
            config.analysis.external.semgrep,
            config.analysis.external.gitleaks && config.analysis.secrets,
            config.analysis.external.osv && config.analysis.dependencies && opts.stages.contains(&Stage::Dependencies),
        );
        let offline = opts.offline || opts.quick;
        let outs: Vec<external::ExternalOutput> = std::thread::scope(|s| {
            let mut hs = Vec::new();
            if do_sg {
                hs.push(s.spawn(|| external::semgrep(&root, &store, timeout)));
            }
            if do_gl {
                hs.push(s.spawn(|| external::gitleaks(&root, &store, timeout)));
            }
            if do_osv {
                hs.push(s.spawn(|| external::osv(&root, &store, timeout, offline)));
            }
            hs.into_iter().filter_map(|h| h.join().ok()).collect()
        });
        for o in outs {
            findings.extend(o.findings);
            stages.push(o.stage);
        }
    }

    let ctx = ExtractContext { facts: &facts, config: &config, org: &org };
    let cache = ProofCache::new(&base, !opts.no_cache);
    let fopts = FormalOptions {
        seed,
        search_budget: if opts.deep { 2_000_000 } else { 200_000 },
        timeout: Duration::from_secs(config.verification.timeout),
        parallel: config.verification.parallel,
        max_proofs: config.verification.max_proofs,
        hints_dir: Some(root.join(".proof-it").join("proof-hints")),
    };
    let mut results = Vec::new();
    let mut extractions = std::collections::HashMap::new();
    if opts.stages.contains(&Stage::Formal) && config.analysis.formal {
        let out = run_formal(&props, &ctx, &store, &cache, &fopts);
        results = out.results;
        extractions = out.extractions;
        stages.push(out.stage);
    }
    if opts.stages.contains(&Stage::Selfcheck) && !results.is_empty() {
        let (fs, st) = selftest::model_self_check(&mut results, &extractions, seed);
        findings.extend(fs);
        stages.push(st);
    }
    let mut attack_summary = None;
    if opts.stages.contains(&Stage::Attack) && config.analysis.fuzzing {
        let allowed = opts.allow_exec || config.testing.allow_execution;
        if opts.safe || !allowed {
            let why = if opts.safe {
                "--safe: repository code is never executed"
            } else {
                "executing repository code is opt-in (--allow-exec or testing.allow_execution); model-level counterexamples are still reported"
            };
            stages.push(StageRun::new("attack", StageStatus::Skipped, 0, why));
        } else {
            match Executor::new(&root, &project.files, allowed, opts.safe) {
                Ok(exec) => {
                    let iterations = if opts.deep {
                        config.testing.iterations * 4
                    } else if opts.quick {
                        config.testing.iterations.min(50)
                    } else {
                        config.testing.iterations
                    };
                    let a = attack::run(&mut results, &extractions, &exec, &store, seed, iterations);
                    findings.extend(a.findings);
                    stages.push(a.stage);
                    attack_summary = Some(AttackSummary { replays: a.replays, reproduced: a.reproduced, cases: a.cases });
                }
                Err(e) => stages.push(StageRun::new(
                    "attack",
                    if matches!(e, Error::Usage(_)) { StageStatus::Skipped } else { StageStatus::Failed },
                    0,
                    e.to_string(),
                )),
            }
        }
    }
    let mut mutation = None;
    if opts.stages.contains(&Stage::Mutation) {
        let (m, st) = selftest::mutation(
            &props,
            &facts,
            &project.files,
            &results,
            &extractions,
            &ctx,
            &cache,
            &FormalOptions { search_budget: 50_000, ..fopts.clone() },
            if opts.deep { 200 } else { 40 },
        );
        mutation = Some(m);
        stages.push(st);
    }

    apply_suppressions(&mut findings, &mut results, &suppressions, &org);

    // Change assessment.
    let baseline_report: Option<Report> = match &opts.baseline {
        None => None,
        Some(b) if b.ends_with(".json") => {
            Some(serde_json::from_str(&std::fs::read_to_string(b).map_err(|e| Error::io(b, e))?).map_err(|e| Error::Usage(format!("{b}: {e}")))?)
        }
        Some(b) => Some(RunStore::open(&base, b)?.read_json("report.json")?),
    };
    let mut change_assessment = None;
    if let Some(range) = &opts.diff {
        let changed = project::changed_files(&root, range)?;
        let (code_files, policy_files): (Vec<String>, Vec<String>) = changed.iter().cloned().partition(|f| !change::is_policy_file(f));
        let affected = change::affected_modules(&facts, &code_files);
        let aff_set: BTreeSet<&str> = affected.iter().map(String::as_str).collect();
        for r in &mut results {
            let files = extractions.get(&key(&r.property_id, &r.target)).map(|e| e.files.clone()).unwrap_or_default();
            r.in_change = Some(files.iter().any(|f| aff_set.contains(f.as_str())) || r.location.as_ref().is_some_and(|l| aff_set.contains(l.file.as_str())));
        }
        for f in &mut findings {
            f.baseline = Some(if f.location.as_ref().is_some_and(|l| aff_set.contains(l.file.as_str()) || changed.contains(&l.file)) {
                BaselineState::New
            } else {
                BaselineState::Existing
            });
        }
        let affected_props = change::affected_properties(&results, &findings, &extractions, &affected, &facts, &props);
        let base_rev = range.split("...").next().unwrap_or(range).split("..").next().unwrap_or(range).to_owned();
        let base_cfg: Config =
            project::file_at(&root, &base_rev, ".proof-it/config.yaml").and_then(|t| parse_yaml(&t, Path::new("base config")).ok()).unwrap_or_default();
        let base_sups: Vec<Suppression> = project::file_at(&root, &base_rev, ".proof-it/suppressions.yaml")
            .and_then(|t| parse_yaml::<serde_json::Value>(&t, Path::new("base suppressions")).ok())
            .and_then(|v| serde_json::from_value(v["suppressions"].clone()).ok())
            .unwrap_or_default();
        let mut policy_changes = change::policy_changes(&base_cfg, &config, &base_sups, &suppressions, &org);
        for pf in policy_files.iter().filter(|p| p.starts_with(".proof-it/properties/") || p.starts_with(".proof-it/proof-hints/")) {
            policy_changes.push(change::PolicyChange { what: format!("verification artifact changed: {pf}"), protected: false });
        }
        let regressions = baseline_report.as_ref().map(|b| change::regressions(&b.results, &results)).unwrap_or_default();
        let attack_ran = stages.iter().any(|s| s.name == "attack" && s.status == StageStatus::Ran);
        let merge = change::decide(
            &org.merge_policy,
            &affected_props,
            &results,
            &findings,
            &affected,
            &regressions,
            &policy_changes,
            attack_ran,
            baseline_report.is_some(),
        );
        change_assessment = Some(ChangeAssessment {
            range: range.clone(),
            agent: opts.agent.clone(),
            changed_files: changed,
            code_files,
            policy_files,
            affected_modules: affected,
            affected_properties: affected_props,
            baseline: baseline_report.as_ref().map(|b| b.run_id.clone()),
            regressions,
            policy_changes,
            merge,
        });
    } else if let Some(b) = &baseline_report {
        let old: HashSet<&str> = b.findings.iter().map(|f| f.id.as_str()).collect();
        for f in &mut findings {
            f.baseline = Some(if old.contains(f.id.as_str()) { BaselineState::Existing } else { BaselineState::New });
        }
        let regs = change::regressions(&b.results, &results);
        let attack_ran = stages.iter().any(|s| s.name == "attack" && s.status == StageStatus::Ran);
        let all_props: Vec<String> = results.iter().map(|r| r.property_id.clone()).collect::<BTreeSet<_>>().into_iter().collect();
        let merge = change::decide(&org.merge_policy, &all_props, &results, &findings, &[], &regs, &[], attack_ran, true);
        change_assessment = Some(ChangeAssessment {
            range: format!("baseline {}", b.run_id),
            agent: opts.agent.clone(),
            changed_files: vec![],
            code_files: vec![],
            policy_files: vec![],
            affected_modules: vec![],
            affected_properties: all_props,
            baseline: Some(b.run_id.clone()),
            regressions: regs,
            policy_changes: vec![],
            merge,
        });
    }

    let scoped = opts.diff.is_some() || opts.baseline.is_some();
    let gaps = coverage_gaps(&facts.parse_errors, &project.skipped, &project.unsupported);
    let mut verdict = verdict::compute(&results, &findings, &stages, &config, scoped, &gaps);
    // Say what is not modeled for the languages that were analysed.
    let go_files = facts.modules.iter().filter(|m| m.language == proof_it_core::facts::Language::Go).count();
    if go_files > 0 {
        verdict.warnings.push(format!(
            "Go ({go_files} file(s)): security detectors only — authorization (AUTHZ-*), state-machine and ledger properties are not modeled for Go code yet"
        ));
        if verdict.verdict == AssuranceVerdict::Passed {
            verdict.verdict = AssuranceVerdict::PassedWithWarnings;
        }
    }
    // The repository may not redefine who is an administrator (see effective_admin_roles).
    if let (roles, Some(ignored)) = proof_it_core::config::effective_admin_roles(&config, &org) {
        verdict.warnings.push(format!(
            "authorization.admin_roles in the repository configuration ({}) was ignored: it would add roles to the trusted admin set ({}). Set admin roles in the organisation policy.",
            if ignored.is_empty() { "empty".to_owned() } else { ignored.join(", ") },
            roles.join(", ")
        ));
        if verdict.verdict == AssuranceVerdict::Passed {
            verdict.verdict = AssuranceVerdict::PassedWithWarnings;
        }
    }
    if let Some(c) = &change_assessment {
        for g in &c.regressions {
            verdict.reasons.push(format!("REGRESSION {} {}: {} → {}", g.property_id, g.target, g.before, g.after));
        }
        for p in c.policy_changes.iter().filter(|p| p.protected) {
            verdict.reasons.push(format!("protected property weakened: {}", p.what));
        }
        if !verdict.reasons.is_empty() {
            verdict.verdict = AssuranceVerdict::Failed;
            verdict.exit_code = proof_it_core::ExitCode::AssuranceFailed as u8;
        }
    }
    // A change whose code was not fully analysed is never eligible for auto-merge.
    if !gaps.is_empty()
        && let Some(c) = change_assessment.as_mut()
        && c.merge.decision == crate::change::MergeDecision::AutoMergeEligible
    {
        c.merge.decision = crate::change::MergeDecision::HumanReviewRequired;
        c.merge.reasons.push(format!("analysis incomplete: {} source file(s) not analysed", gaps.len()));
    }
    let level = verdict::assurance_level(&results, &findings, &stages, &gaps);
    let debt = verdict::proof_debt(&results);
    let max_level = results.iter().map(|r| r.level.0).max().unwrap_or(0);
    let protected = |id: &str| org.protected_properties.iter().any(|p| p.eq_ignore_ascii_case(id));
    let mut options = BTreeMap::new();
    options.insert("safe".into(), opts.safe.into());
    options.insert("allow_exec".into(), opts.allow_exec.into());
    options.insert("quick".into(), opts.quick.into());
    options.insert("deep".into(), opts.deep.into());
    options.insert("offline".into(), opts.offline.into());
    options.insert("diff".into(), opts.diff.clone().into());
    options.insert("baseline".into(), opts.baseline.clone().into());
    options.insert("stages".into(), serde_json::to_value(&opts.stages).unwrap_or_default());
    findings.sort_by(|a, b| {
        b.severity
            .cmp(&a.severity)
            .then_with(|| a.location.as_ref().map(|l| (l.file.clone(), l.line)).cmp(&b.location.as_ref().map(|l| (l.file.clone(), l.line))))
    });
    let report = Report {
        format: REPORT_FORMAT.into(),
        run_id: store.id.clone(),
        run_dir: store.dir.display().to_string(),
        command: opts.command.clone(),
        started_at,
        duration_ms: ms(started),
        project: ProjectInfo {
            root: root.display().to_string(),
            name: if config.project.name.is_empty() { project.name.clone() } else { config.project.name.clone() },
            commit: project.git.as_ref().and_then(|g| g.commit.clone()),
            branch: project.git.as_ref().and_then(|g| g.branch.clone()),
            languages: project.languages.clone(),
            files: project.files.len(),
            functions: facts.function_count(),
            parse_errors: facts.parse_errors.clone(),
            skipped: project.skipped.len(),
        },
        environment: Environment {
            proof_it: proof_it_core::VERSION.into(),
            lean: toolchain().map(|t| t.version.clone()),
            sandbox: sandbox_available(),
            platform: format!("{}-{}", std::env::consts::OS, std::env::consts::ARCH),
        },
        seed,
        options,
        config,
        config_path: loaded.path.map(|p| p.display().to_string()),
        org_policy: org.clone(),
        stages,
        properties: props
            .iter()
            .map(|p| PropertyInfo {
                id: p.id().into(),
                name: p.name().into(),
                category: p.spec.category.clone(),
                severity: p.severity,
                version: p.spec.version,
                source: p.source,
                formal: p.spec.formal.is_some(),
                protected: protected(p.id()),
            })
            .collect(),
        results,
        findings,
        suppressions,
        attack: attack_summary,
        mutation,
        change: change_assessment,
        verdict,
        assurance_level: level,
        proof_debt: debt,
        max_formalization_level: max_level,
    };
    store.write_json("report.json", &report)?;
    store.write_json("results.json", &report.results)?;
    store.write_json("findings.json", &report.findings)?;
    store.write_json("summary.json", &serde_json::json!({ "run_id": report.run_id, "verdict": report.verdict.verdict, "counts": report.verdict.counts, "severities": report.verdict.severities, "assurance_level": report.assurance_level.level, "seed": seed, "commit": report.project.commit, "merge": report.change.as_ref().map(|c| c.merge.decision) }))?;
    store.write_json("metadata.json", &serde_json::json!({ "proof_it": proof_it_core::VERSION, "environment": report.environment, "options": report.options, "project": report.project, "config_path": report.config_path, "org_policy": report.org_policy.source, "property_versions": report.properties.iter().map(|p| (p.id.clone(), p.version)).collect::<BTreeMap<_, _>>(), "stages": report.stages }))?;
    if report.change.is_some() {
        write_change_bundle(&root, &base, &store, &report, opts.diff.as_deref())?;
    }
    Ok(report)
}

/// `.proof-it/changes/<change-id>/`: the machine-readable assurance record of a change.
fn write_change_bundle(root: &Path, base: &Path, store: &RunStore, report: &Report, range: Option<&str>) -> Result<()> {
    let changes = base.join("changes");
    proof_it_core::paths::ensure_real_dir(&changes)?;
    let short = report.project.commit.as_deref().map_or("nocommit", |c| &c[..c.len().min(8)]);
    let id = format!("PI-{}-{short}", report.run_id);
    let dir = changes.join(&id);
    std::fs::create_dir_all(&dir).map_err(|e| Error::io(&dir, e))?;
    let Some(c) = &report.change else {
        return Ok(());
    };
    let manifest = serde_json::json!({
        "format": "proof-it/change@1",
        "change_id": id,
        "range": c.range,
        "commit": report.project.commit,
        "agent": c.agent,
        "run_id": report.run_id,
        "run_dir": report.run_dir,
        "merge_decision": c.merge.decision,
        "merge_reasons": c.merge.reasons,
        "verdict": report.verdict.verdict,
        "assurance_level": report.assurance_level,
        "changed_files": c.changed_files,
        "affected_modules": c.affected_modules.len(),
        "affected_properties": c.affected_properties,
        "properties_proven": report.results.iter().filter(|r| r.status() == ProofStatus::Proven && c.affected_properties.contains(&r.property_id)).count(),
        "properties_violated": report.results.iter().filter(|r| r.status() == ProofStatus::Violated && c.affected_properties.contains(&r.property_id)).count(),
        "properties_unproven": report.results.iter().filter(|r| r.status() == ProofStatus::Unproven && c.affected_properties.contains(&r.property_id)).count(),
        "security_findings_in_change": report.findings.iter().filter(|f| f.baseline == Some(BaselineState::New) && f.suppressed.is_none()).count(),
        "counterexamples": report.results.iter().filter(|r| r.counterexample.is_some()).count(),
        "regressions": c.regressions,
        "policy_changes": c.policy_changes,
        "trust_note": "Statuses come from Proof-It's pipeline (Lean kernel, analyzers, executed tests). Claims made by the author of the change are not evidence.",
    });
    let write = |name: &str, v: &serde_json::Value| {
        std::fs::write(dir.join(name), serde_json::to_string_pretty(v).unwrap_or_default()).map_err(|e| Error::io(dir.join(name), e))
    };
    write("manifest.json", &manifest)?;
    write(
        "properties.json",
        &serde_json::to_value(report.results.iter().filter(|r| c.affected_properties.contains(&r.property_id)).collect::<Vec<_>>()).unwrap_or_default(),
    )?;
    write("report.json", &serde_json::to_value(report).unwrap_or_default())?;
    if let Some(range) = range
        && let Ok(patch) = project::diff_patch(root, range)
    {
        let _ = std::fs::write(dir.join("diff.patch"), patch);
    }
    for sub in ["proofs", "counterexamples"] {
        let from = store.dir.join(sub);
        let to = dir.join(sub);
        let _ = std::fs::create_dir_all(&to);
        if let Ok(rd) = std::fs::read_dir(&from) {
            for e in rd.flatten() {
                let _ = std::fs::copy(e.path(), to.join(e.file_name()));
            }
        }
    }
    Ok(())
}

/// Source files that were not analysed: unparseable, or skipped by size/count limits.
/// Non-source files skipped (large data files, images) are not gaps.
pub fn coverage_gaps(parse_errors: &[(String, String)], skipped: &[(String, String)], unsupported: &[(String, String)]) -> Vec<String> {
    let source = |f: &str| {
        let ext = std::path::Path::new(f).extension().and_then(|e| e.to_str()).unwrap_or("").to_ascii_lowercase();
        proof_it_core::facts::Language::from_extension(&ext).is_some() && !f.ends_with(".min.js") && !f.ends_with(".d.ts")
    };
    parse_errors
        .iter()
        .map(|(f, e)| format!("{f}: could not be parsed ({e})"))
        .chain(skipped.iter().filter(|(f, _)| source(f)).map(|(f, why)| format!("{f}: not analysed ({why})")))
        .chain(unsupported.iter().map(|(f, lang)| format!("{f}: not analysed ({lang} is not supported by Proof-It yet)")))
        .collect()
}

#[cfg(test)]
mod tests {
    #[test]
    fn report_round_trips_through_json() {
        // A report written by one run must be readable as a baseline by the next.
        let dir = tempfile::tempdir().expect("tmp");
        std::fs::write(dir.path().join("a.ts"), "export function f(x: number) { return x + 1; }").expect("w");
        let opts = super::Options {
            path: dir.path().into(),
            command: "assure".into(),
            stages: [super::Stage::Static, super::Stage::Security].into_iter().collect(),
            seed: None,
            safe: true,
            allow_exec: false,
            quick: true,
            deep: false,
            offline: true,
            properties: vec![],
            diff: None,
            baseline: None,
            out_dir: None,
            no_cache: true,
            timeout: None,
            policy: None,
            agent: None,
        };
        let r = super::run(&opts).expect("run");
        let text = serde_json::to_string(&r).expect("ser");
        let back: super::Report = serde_json::from_str(&text).expect("report must deserialize");
        assert_eq!(back.run_id, r.run_id);
    }
}
