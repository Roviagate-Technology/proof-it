//! End-to-end: TypeScript source → facts → obligations → Lean kernel.
//! Skipped (with a message) when Lean is not installed.

use proof_it_core::config::{Config, OrgPolicy};
use proof_it_core::facts::ProgramFacts;
use proof_it_core::property::Registry;
use proof_it_core::store::{ProofCache, RunStore, evidence_base};
use proof_it_core::types::ProofStatus;
use proof_it_model::extract::ExtractContext;
use proof_it_model::formal::{FormalOptions, run};
use std::collections::{HashMap, HashSet};
use std::time::Duration;

#[test]
fn sample_verdicts() {
    if proof_it_model::lean::runner::toolchain().is_none() {
        eprintln!("SKIPPED: Lean not installed");
        return;
    }
    let text = include_str!("../../lang-ts/tests/fixtures/sample.ts");
    let a = proof_it_lang_ts::analyze("src/sample.ts", text, &HashSet::new()).expect("parse");
    let facts = ProgramFacts { modules: vec![a.facts], texts: vec![("src/sample.ts".into(), a.text)], parse_errors: vec![] };
    let reg = Registry::load(None).expect("library");
    let props: Vec<_> = reg.select(&["STATE-001".into(), "PAY-001".into(), "PAY-003".into(), "AUTHZ-001".into()], &[]);
    let dir = tempfile::tempdir().expect("tmp");
    let base = evidence_base(dir.path(), None).expect("base");
    let store = RunStore::create(&base).expect("store");
    let cfg = Config::default();
    let org = OrgPolicy::default();
    let ctx = ExtractContext { facts: &facts, config: &cfg, org: &org };
    let opts = FormalOptions { seed: 1, search_budget: 200_000, timeout: Duration::from_secs(120), parallel: true, max_proofs: 100, hints_dir: None };
    let out = run(&props, &ctx, &store, &ProofCache::new(&base, false), &opts);
    let by: HashMap<String, ProofStatus> = out.results.iter().map(|r| (format!("{} {}", r.property_id, r.target), r.status())).collect();
    for r in &out.results {
        eprintln!("{:<10} {:<9} {}\n    {}", r.status().label(), r.property_id, r.target, r.reason);
    }
    let get = |p: &str, t: &str| by.iter().find(|(k, _)| k.starts_with(p) && k.contains(t)).map(|(_, v)| *v);
    assert_eq!(get("STATE-001", "CANCELLED"), Some(ProofStatus::Proven));
    assert_eq!(get("STATE-001", "RESOLVED"), Some(ProofStatus::Violated));
    assert_eq!(get("PAY-001", "transfer"), Some(ProofStatus::Proven));
    assert_eq!(get("PAY-003", "transfer"), Some(ProofStatus::Violated));
    assert_eq!(get("AUTHZ-001", "/records/:id"), Some(ProofStatus::Violated));
    assert_eq!(get("AUTHZ-001", "/safe/:id"), Some(ProofStatus::Proven));
    // Every PROVEN result carries a kernel-checked non-vacuity witness.
    for r in out.results.iter().filter(|r| r.status() == ProofStatus::Proven) {
        let q = r.quality.as_ref().expect("quality");
        assert!(q.kernel_checked);
        assert_eq!(q.non_vacuity, proof_it_core::types::NonVacuity::KernelCheckedWitness, "{}", r.target);
    }
    // Every VIOLATED result carries a Lean-certified counterexample.
    for r in out.results.iter().filter(|r| r.status() == ProofStatus::Violated) {
        assert!(r.counterexample.as_ref().and_then(|c| c.lean_certificate.as_ref()).is_some(), "{}", r.target);
    }
}

/// AUTHZ-002 status of `GET /admin/reports`, served by a router that calls
/// `router.use(authMiddleware, adminMiddleware)` with `adminMiddleware` imported
/// from a file whose body is `admin_mw`. `None` when Lean is not installed.
fn admin_route_status(admin_mw: &str) -> Option<ProofStatus> {
    admin_route_status_with(admin_mw, &Config::default(), &OrgPolicy::default())
}

fn admin_route_status_with(admin_mw: &str, cfg: &Config, org: &OrgPolicy) -> Option<ProofStatus> {
    if proof_it_model::lean::runner::toolchain().is_none() {
        eprintln!("SKIPPED: Lean not installed");
        return None;
    }
    let files = [
        ("src/middleware/admin.ts", admin_mw),
        (
            "src/middleware/auth.ts",
            r#"
import jwt from 'jsonwebtoken';
export const authMiddleware = (req: any, res: any, next: any) => {
  const token = req.header('Authorization');
  if (!token) return res.status(401).json({ error: 'no token' });
  req.user = jwt.verify(token, process.env.JWT_SECRET as string);
  next();
};
"#,
        ),
        (
            "src/routes/admin.ts",
            r#"
import { Router } from 'express';
import { authMiddleware } from '../middleware/auth';
import { adminMiddleware } from '../middleware/admin';
const router = Router();
router.use(authMiddleware, adminMiddleware);
router.get('/admin/reports', async (req: any, res: any) => {
  const reports = await db.report.findMany({});
  res.json(reports);
});
export default router;
"#,
        ),
    ];
    let known: HashSet<String> = files.iter().map(|(p, _)| (*p).to_owned()).collect();
    let analysed: Vec<_> = files.iter().map(|(p, t)| proof_it_lang_ts::analyze(p, t, &known).expect("parse")).collect();
    let mount = analysed[2].facts.mounts.first().expect("router.use recorded");
    assert_eq!(mount.target_module.as_deref(), Some("src/middleware/admin.ts"));
    assert_eq!(mount.target_text.as_deref(), Some("adminMiddleware"));

    let facts = ProgramFacts {
        modules: analysed.iter().map(|a| a.facts.clone()).collect(),
        texts: analysed.iter().map(|a| (a.facts.file.clone(), a.text.clone())).collect(),
        parse_errors: vec![],
    };
    let reg = Registry::load(None).expect("library");
    let props: Vec<_> = reg.select(&["AUTHZ-002".into()], &[]);
    let dir = tempfile::tempdir().expect("tmp");
    let base = evidence_base(dir.path(), None).expect("base");
    let store = RunStore::create(&base).expect("store");
    let ctx = ExtractContext { facts: &facts, config: cfg, org };
    let opts = FormalOptions { seed: 1, search_budget: 200_000, timeout: Duration::from_secs(120), parallel: true, max_proofs: 100, hints_dir: None };
    let out = run(&props, &ctx, &store, &ProofCache::new(&base, false), &opts);
    let r = out.results.iter().find(|r| r.target.contains("/admin/reports")).expect("route analysed");
    eprintln!("{} {} {}", r.status().label(), r.target, r.reason);
    Some(r.status())
}

/// `router.use(auth, adminMiddleware)` with imported middleware: the last
/// argument is middleware, not a mounted router, and must guard the routes.
/// Before, it was taken for a router module and the guard was dropped, so a
/// role-checked admin route was reported VIOLATED.
#[test]
fn imported_middleware_in_router_use_guards_routes() {
    let Some(status) = admin_route_status(
        r#"
export const adminMiddleware = (req: any, res: any, next: any) => {
  if (!req.user) return res.status(401).json({ error: 'auth' });
  if (req.user.role !== 'admin') return res.status(403).json({ error: 'admin only' });
  next();
};
"#,
    ) else {
        return;
    };
    assert_eq!(status, ProofStatus::Proven, "the role check in adminMiddleware guards the route");
}

/// Recognising imported middleware must not turn a fake guard into a proof:
/// a middleware named like an admin guard whose code cannot enforce a role
/// leaves the admin route VIOLATED.
#[test]
fn fake_admin_guards_in_router_use_do_not_protect() {
    let fakes = [
        // Does nothing.
        ("passes everything", "export const adminMiddleware = (req: any, res: any, next: any) => { next(); };"),
        // Reads the role but never denies.
        ("reads the role, never denies", "export const adminMiddleware = (req: any, res: any, next: any) => { console.log(req.user.role); next(); };"),
        // Denies only unauthenticated requests: any signed-in user passes.
        ("authentication only", "export const adminMiddleware = (req: any, res: any, next: any) => { if (!req.user) return res.status(401).end(); next(); };"),
        // The admin word only in a comment and a log message.
        (
            "admin only in comments",
            "// requires role 'admin'\nexport const adminMiddleware = (req: any, res: any, next: any) => { if (!req.user) return res.status(401).end(); next(); };",
        ),
    ];
    for (what, code) in fakes {
        let Some(status) = admin_route_status(code) else {
            return;
        };
        assert_eq!(status, ProofStatus::Violated, "fake guard ({what}) must not protect the route");
    }
}

/// Guards that check a role but would let a non-admin through must never be
/// PROVEN to require an admin.
#[test]
fn unsound_role_guards_are_not_proven() {
    let cases = [
        (
            "admits a non-admin role",
            "export const adminMiddleware = (req: any, res: any, next: any) => { if (!['admin', 'user'].includes(req.user.role)) return res.status(403).end(); next(); };",
        ),
        (
            "admits a non-admin role via a constant",
            "const ALLOWED = ['admin', 'user'];\nexport const adminMiddleware = (req: any, res: any, next: any) => { if (!ALLOWED.includes(req.user.role)) return res.status(403).end(); next(); };",
        ),
        (
            "calls next() before checking",
            "export const adminMiddleware = (req: any, res: any, next: any) => { next(); if (req.user.role !== 'admin') return res.status(403).end(); };",
        ),
        (
            "denies only admins",
            "export const adminMiddleware = (req: any, res: any, next: any) => { if (req.user.role === 'admin') return res.status(403).end(); next(); };",
        ),
        (
            "check in a branch that may not run",
            "export const adminMiddleware = (req: any, res: any, next: any) => { if (req.query.strict) { if (req.user.role !== 'admin') return res.status(403).end(); } next(); };",
        ),
    ];
    for (what, code) in cases {
        let Some(status) = admin_route_status(code) else {
            return;
        };
        assert_ne!(status, ProofStatus::Proven, "{what}: must not be PROVEN");
    }
}

/// The repository configuration is untrusted: declaring a non-admin role an
/// admin there must not produce a proof.
#[test]
fn repository_config_cannot_make_user_an_admin() {
    let mut cfg = Config::default();
    cfg.authorization.admin_roles = vec!["admin".into(), "user".into()];
    let Some(status) = admin_route_status_with(
        "export const adminMiddleware = (req: any, res: any, next: any) => { if (!['admin', 'user'].includes(req.user.role)) return res.status(403).end(); next(); };",
        &cfg,
        &OrgPolicy::default(),
    ) else {
        return;
    };
    assert_ne!(status, ProofStatus::Proven);
}

/// A guard whose admitted roles are read exactly from the code (inline or an
/// `export const` list) and are all admin roles is PROVEN.
#[test]
fn exact_admin_role_guards_are_proven() {
    let cases = [
        "export const adminMiddleware = (req: any, res: any, next: any) => { if (!['admin', 'super_admin'].includes(req.user.role)) return res.status(403).end(); next(); };",
        "export const ADMIN = ['admin', 'super_admin'] as const;\nexport const adminMiddleware = (req: any, res: any, next: any) => {\n  if (!req.user) return res.status(401).end();\n  if (!(ADMIN as readonly string[]).includes(req.user.role)) { return res.status(403).json({ error: 'admin only' }); }\n  next();\n};",
        "export const adminMiddleware = (req: any, res: any, next: any) => { if (req.user.role !== 'admin' && req.user.role !== 'super_admin') throw new Error('forbidden'); next(); };",
    ];
    for code in cases {
        let Some(status) = admin_route_status(code) else {
            return;
        };
        assert_eq!(status, ProofStatus::Proven, "{code}");
    }
}

/// `organization_admin` is an admin only if the trusted organisation policy
/// says so: by default a guard that admits it is not an admin check.
#[test]
fn extra_admin_roles_come_only_from_the_trusted_policy() {
    let guard = "export const ADMIN_ROLES = ['admin', 'super_admin', 'organization_admin'] as const;\nexport const adminMiddleware = (req: any, res: any, next: any) => {\n  if (!req.user) return res.status(401).json({ error: 'auth' });\n  if (!(ADMIN_ROLES as readonly string[]).includes(req.user.role)) return res.status(403).json({ error: 'admin' });\n  next();\n};";
    let Some(default) = admin_route_status(guard) else {
        return;
    };
    assert_eq!(default, ProofStatus::Violated, "organization_admin is not an admin role by default");

    // The repository cannot declare it.
    let mut cfg = Config::default();
    cfg.authorization.admin_roles = vec!["admin".into(), "super_admin".into(), "organization_admin".into()];
    let repo = admin_route_status_with(guard, &cfg, &OrgPolicy::default()).expect("lean");
    assert_eq!(repo, ProofStatus::Violated, "the repository config cannot add admin roles");

    // The organisation policy can.
    let org = OrgPolicy { admin_roles: Some(vec!["admin".into(), "super_admin".into(), "organization_admin".into()]), ..OrgPolicy::default() };
    let trusted = admin_route_status_with(guard, &Config::default(), &org).expect("lean");
    assert_eq!(trusted, ProofStatus::Proven);
}

/// AUTHZ-002 status of `DELETE /admin/users/:id` in a single-file app.
fn single_file_admin_status(code: &str) -> Option<ProofStatus> {
    if proof_it_model::lean::runner::toolchain().is_none() {
        eprintln!("SKIPPED: Lean not installed");
        return None;
    }
    let a = proof_it_lang_ts::analyze("src/app.ts", code, &HashSet::new()).expect("parse");
    let facts = ProgramFacts { modules: vec![a.facts], texts: vec![("src/app.ts".into(), a.text)], parse_errors: vec![] };
    let reg = Registry::load(None).expect("library");
    let props: Vec<_> = reg.select(&["AUTHZ-002".into()], &[]);
    let dir = tempfile::tempdir().expect("tmp");
    let base = evidence_base(dir.path(), None).expect("base");
    let store = RunStore::create(&base).expect("store");
    let (cfg, org) = (Config::default(), OrgPolicy::default());
    let ctx = ExtractContext { facts: &facts, config: &cfg, org: &org };
    let opts = FormalOptions { seed: 1, search_budget: 200_000, timeout: Duration::from_secs(120), parallel: true, max_proofs: 100, hints_dir: None };
    let out = run(&props, &ctx, &store, &ProofCache::new(&base, false), &opts);
    let r = out.results.iter().find(|r| r.target.contains("/admin/users")).expect("route analysed");
    eprintln!("{} {} {}", r.status().label(), r.target, r.reason);
    Some(r.status())
}

/// Role factories (`requireRole('admin')`): proven only when the inner guard
/// denies unless the role is among the factory's arguments AND every argument
/// at the call is a literal admin role.
#[test]
fn role_factories_are_read_from_the_call_site() {
    let app = |factory: &str, call: &str| {
        format!(
            "import express from 'express';\nconst app = express();\nconst db: any = {{}};\n{factory}\napp.delete('/admin/users/:id', {call}, async (req: any, res: any) => {{\n  await db.users.delete({{ where: {{ id: req.params.id }} }});\n  res.json({{ ok: true }});\n}});\n"
        )
    };
    let real = "const requireRole = (...roles: string[]) => (req: any, res: any, next: any) => {\n  if (!req.user || !roles.includes(req.user.role)) {\n    return res.status(403).json({ error: 'forbidden' });\n  }\n  next();\n};";
    let Some(ok) = single_file_admin_status(&app(real, "requireRole('admin', 'super_admin')")) else {
        return;
    };
    assert_eq!(ok, ProofStatus::Proven, "literal admin roles at the call");
    let array = "const requireRoles = (roles: string[]) => (req: any, res: any, next: any) => {\n  if (!roles.includes(req.user.role)) return res.status(403).end();\n  next();\n};";
    assert_eq!(single_file_admin_status(&app(array, "requireRoles(['admin'])")), Some(ProofStatus::Proven), "array argument");

    let bad = [
        (real, "requireRole('admin', 'user')", "a non-admin role at the call"),
        (real, "requireRole(ROLE)", "a variable at the call"),
        (real, "requireRole(...ROLES)", "a spread at the call"),
        (
            "const requireRole = (...roles: string[]) => (req: any, res: any, next: any) => {\n  if (!req.user.role) return res.status(403).end();\n  next();\n};",
            "requireRole('admin')",
            "a factory that ignores its argument",
        ),
        (
            "const requireRole = (...roles: string[]) => (req: any, res: any, next: any) => {\n  if (roles.includes(req.user.role)) return res.status(403).end();\n  next();\n};",
            "requireRole('admin')",
            "a factory that denies the listed roles",
        ),
    ];
    for (factory, call, what) in bad {
        let status = single_file_admin_status(&app(factory, call)).expect("lean");
        assert_ne!(status, ProofStatus::Proven, "{what} must not be PROVEN");
    }
}
