//! Authorization extraction for HTTP handlers.
//!
//! AUTHZ-001: for each authenticated handler that loads a resource by a
//! client-supplied identifier and sends it back, prove
//!     PC(sink) → owner = principal ∨ role ∈ adminRoles
//! for every response that contains the resource.
//! AUTHZ-002: for handlers under an /admin path, prove every successful
//! response requires role ∈ adminRoles.
//!
//! Checks that mention the principal or the resource but cannot be interpreted
//! become opaque gates (→ UNPROVEN rather than VIOLATED). Input validation and
//! authentication-presence checks are satisfiable preconditions.

use super::{ExtractContext, Extraction, show_cond};
use crate::eval::{Assignment, Evaluator, Value};
use crate::ir::*;
use proof_it_core::facts::*;
use proof_it_core::property::{Extractor, Property};
use proof_it_core::types::{CounterexampleStep, SourceLocation};
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, LazyLock};

static AUTH_MW: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?i)auth|jwt|token|session|protect|login|passport|guard|requireUser|ensureLoggedIn|verifyUser|isLoggedIn|authenticated").expect("static regex")
});
static AUTHZ_MW: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"(?i)owner|permission|\bacl|access_?polic|authz|rbac|role|abac|\bcan[A-Z_]|authori[sz]\w*\(\s*[^)\s]").expect("static regex"));
/// Infrastructure middleware that never makes an authorization decision.
static INFRA_MW: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?i)helmet|featurePolicy|permissionsPolicy|cors|bodyParser|express\.(json|urlencoded|static)|compression|morgan|cookieParser|rateLimit|slowDown|multer|upload|serveIndex|logger|i18n|csrf").expect("static regex")
});
static ADMIN_MW: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"(?i)admin|superuser|staff").expect("static regex"));
static GUARD_CALL: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"(?i)authori[sz]|assert|ensure|check|verify|permit|guard|can[A-Z]|require|own").expect("static regex"));

struct Env {
    principal_paths: BTreeSet<String>,
    /// Request ids used as lookup keys (for tenant scoping).
    lookup_ids: BTreeSet<String>,
    /// Tenant scoping recognised (`req.user.orgId === req.params.id` guarding a lookup by that id).
    tenant_scoped: Vec<String>,
    principal_bases: BTreeSet<String>,
    request_prefixes: Vec<String>,
    request_params: BTreeSet<String>,
    resource: BTreeSet<String>,
    ownership: BTreeSet<String>,
    admin_roles: Vec<String>,
    guard_fns: BTreeSet<String>,
    vars: BTreeMap<String, ModelVar>,
    role_members: Vec<String>,
    gates: BTreeMap<String, String>,
    uses_role: bool,
}

impl Env {
    fn gate(&mut self, text: &str) -> Expr {
        let t: String = text.split_whitespace().collect::<Vec<_>>().join(" ").chars().take(120).collect();
        let n = self.gates.len() + 1;
        let name = self.gates.entry(t.clone()).or_insert_with(|| format!("gate{n}")).clone();
        self.vars.entry(name.clone()).or_insert_with(|| ModelVar::opaque(&name, Sort::Bool, format!("unanalysed check: {t}")));
        var(&name)
    }
    /// A condition unrelated to authorization (input validation, feature flags): a free
    /// boolean, NOT opaque — a violation may choose its value (assumed satisfiable).
    fn free(&mut self, text: &str) -> Expr {
        let t: String = text.split_whitespace().collect::<Vec<_>>().join(" ").chars().take(120).collect();
        let n = self.vars.keys().filter(|k| k.starts_with("cond")).count() + 1;
        let existing = self.vars.values().find(|v| v.name.starts_with("cond") && v.meaning.ends_with(&t)).map(|v| v.name.clone());
        let name = existing.unwrap_or_else(|| format!("cond{n}"));
        self.vars
            .entry(name.clone())
            .or_insert_with(|| ModelVar::new(&name, Sort::Bool, format!("condition not involving authorization (assumed satisfiable): {t}")));
        var(&name)
    }

    fn role(&mut self, lit: &str) -> Expr {
        self.uses_role = true;
        if !self.role_members.iter().any(|m| m == lit) {
            self.role_members.push(lit.to_owned());
        }
        eq(var("role"), enum_lit("Role", lit))
    }
    fn is_admin(&mut self) -> Expr {
        self.uses_role = true;
        let roles: Vec<String> = self.admin_roles.to_vec();
        or(roles.iter().map(|r| self.role(r)).collect())
    }
    fn found(&mut self) -> Expr {
        self.vars.entry("found".into()).or_insert_with(|| ModelVar::new("found", Sort::Bool, "the lookup returned a resource"));
        var("found")
    }
    fn request_var(&mut self, path: &str) -> String {
        let last = path.rsplit('.').next().unwrap_or("id");
        let name = format!("req_{}", last.chars().map(|c| if c.is_alphanumeric() { c } else { '_' }).collect::<String>());
        self.vars.entry(name.clone()).or_insert_with(|| ModelVar::new(&name, Sort::Nat, format!("client-supplied {path}")));
        name
    }
    /// A request field that identifies a resource: any route parameter, or a
    /// query/body field named like an identifier (not pagination/filters).
    fn is_request_id(&self, p: &str) -> bool {
        if !self.is_request(p) || self.principal_paths.contains(p) {
            return false;
        }
        if p.contains(".params.") || self.request_params.contains(p.split(['.', '[']).next().unwrap_or("")) {
            return true;
        }
        let last = p.rsplit('.').next().unwrap_or("");
        let l = last.to_ascii_lowercase();
        l == "id" || l.ends_with("_id") || last.ends_with("Id") || l.ends_with("uuid") || l.ends_with("slug") || l.ends_with("key") || l == "ids"
    }

    fn is_request(&self, p: &str) -> bool {
        self.request_prefixes.iter().any(|pre| p.starts_with(pre.as_str())) || self.request_params.contains(p.split(['.', '[']).next().unwrap_or(""))
    }
    fn is_principal(&self, v: &Val) -> bool {
        matches!(v, Val::Path { path } if self.principal_paths.contains(path))
    }
    fn is_owner_field(&self, v: &Val) -> bool {
        let Val::Path { path } = v else { return false };
        let cleaned: String = path.split('[').map(|s| s.split_once(']').map_or(s, |(_, r)| r)).collect();
        let parts: Vec<&str> = cleaned.split('.').filter(|s| !s.is_empty()).collect();
        if parts.len() < 2 || !self.resource.contains(parts[0]) {
            return false;
        }
        let field = parts.last().map(|f| f.to_ascii_lowercase()).unwrap_or_default();
        // A user-like record is owned by itself: `user.id === req.user.id`.
        let self_owned = parts.len() == 2 && matches!(field.as_str(), "id" | "_id" | "uuid") && {
            let n = parts[0].to_ascii_lowercase();
            ["user", "account", "profile", "member", "customer", "person", "me"].iter().any(|k| n.contains(k))
        };
        self.ownership.contains(&field) || self_owned
    }
    fn is_role(&self, v: &Val) -> bool {
        matches!(v, Val::Path { path } if self.principal_bases.iter().any(|b| ["role", "type", "userType", "accountType"].iter().any(|f| *path == format!("{b}.{f}"))))
    }
    fn is_admin_flag(&self, v: &Val) -> bool {
        matches!(v, Val::Path { path } if self.principal_bases.iter().any(|b| ["isAdmin", "admin", "isSuperuser"].iter().any(|f| *path == format!("{b}.{f}"))))
    }
    fn mentions(&self, c: &Cond) -> bool {
        c.all_paths().iter().any(|p| {
            let head = p.split(['.', '[']).next().unwrap_or("");
            self.resource.contains(head) || self.principal_bases.iter().any(|b| p == b || p.starts_with(&format!("{b}.")))
        })
    }

    /// `None` = no information (a satisfiable precondition such as input validation).
    fn interp(&mut self, c: &Cond) -> Option<Expr> {
        match c {
            Cond::Not { c: inner } => {
                if let Cond::Truthy { v: Val::Path { path } } = &**inner {
                    if self.resource.contains(path) {
                        return Some(not(self.found()));
                    }
                    if self.principal_bases.contains(path) || self.principal_paths.contains(path) {
                        return None; // `!req.user`: authentication check
                    }
                }
                self.interp(inner).map(not)
            }
            Cond::Truthy { v } => {
                if let Val::Path { path } = v
                    && self.resource.contains(path)
                {
                    return Some(self.found());
                }
                if self.is_admin_flag(v) {
                    return Some(self.is_admin());
                }
                self.mentions(c).then(|| self.gate(&show_cond(c)))
            }
            Cond::And { cs } => {
                let parts: Vec<Expr> = cs.iter().filter_map(|x| self.interp(x)).collect();
                (!parts.is_empty()).then(|| and(parts))
            }
            Cond::Or { cs } => {
                let parts: Vec<Option<Expr>> = cs.iter().map(|x| self.interp(x)).collect();
                if parts.iter().all(Option::is_none) {
                    return None; // pure input validation
                }
                // Disjuncts unrelated to authorization are free (satisfiable) conditions.
                let parts: Vec<Expr> = cs.iter().zip(parts).map(|(x, p)| p.unwrap_or_else(|| self.free(&show_cond(x)))).collect();
                Some(or(parts))
            }
            Cond::InList { list, item } if self.is_role(item) => {
                let lits: Vec<String> = list.clone();
                Some(or(lits.iter().map(|l| self.role(l)).collect()))
            }
            Cond::Cmp { op: op @ (CmpOp::Eq | CmpOp::Ne), l, r } => {
                let wrap = |e: Expr| if *op == CmpOp::Ne { not(e) } else { e };
                if (self.is_owner_field(l) && self.is_principal(r)) || (self.is_owner_field(r) && self.is_principal(l)) {
                    return Some(wrap(eq(var("owner"), var("principal"))));
                }
                for (a, b) in [(l, r), (r, l)] {
                    if self.is_role(a)
                        && let Some(lit) = b.literal()
                    {
                        let lit = lit.to_owned();
                        return Some(wrap(self.role(&lit)));
                    }
                    if let Val::Path { path } = a
                        && self.resource.contains(path)
                        && matches!(b, Val::Null | Val::Undefined)
                    {
                        let f = self.found();
                        return Some(wrap(not(f)));
                    }
                    if let (Val::Len { path }, Val::Int { v: 0 }) = (a, b)
                        && self.resource.contains(path)
                    {
                        let f = self.found();
                        return Some(wrap(not(f)));
                    }
                    // Tenant scoping: an attribute of the principal (req.user.organizationId) equals the
                    // id the resource is looked up by ⇒ the resource belongs to the principal's tenant.
                    if let (Val::Path { path: pa }, Val::Path { path: pb }) = (a, b) {
                        let principal_attr = self.principal_bases.iter().any(|base| pa.starts_with(&format!("{base}.")));
                        if principal_attr && !self.principal_paths.contains(pa) && self.lookup_ids.contains(pb) {
                            self.tenant_scoped.push(format!("{pa} === {pb}"));
                            return Some(wrap(eq(var("owner"), var("principal"))));
                        }
                    }
                    if self.is_principal(a)
                        && let Val::Path { path } = b
                        && self.is_request(path)
                    {
                        let rv = self.request_var(path);
                        return Some(wrap(eq(var("principal"), var(&rv))));
                    }
                }
                self.mentions(c).then(|| self.gate(&show_cond(c)))
            }
            Cond::Call { callee, args, text } => {
                let last = callee.rsplit('.').next().unwrap_or(callee);
                if self.guard_fns.contains(last) {
                    return Some(eq(var("owner"), var("principal")));
                }
                if last == "includes" && args.first().and_then(Val::literal).is_some_and(|l| self.admin_roles.iter().any(|r| r == l)) {
                    let base = callee.trim_end_matches(".includes");
                    if self.principal_bases.iter().any(|b| base == format!("{b}.roles")) {
                        return Some(self.is_admin());
                    }
                }
                self.mentions(c).then(|| self.gate(text))
            }
            _ => self.mentions(c).then(|| self.gate(&show_cond(c))),
        }
    }

    fn guard_expr(&mut self, g: &Guard) -> Option<Expr> {
        match g.kind {
            GuardKind::Branch | GuardKind::EarlyExit => self.interp(&g.cond).map(|e| if g.positive { e } else { not(e) }),
            GuardKind::Case => {
                let Cond::Or { cs } = &g.cond else {
                    return None;
                };
                let mut lits = Vec::new();
                for c in cs {
                    if let Cond::Cmp { l, r, .. } = c {
                        if !self.is_role(l) {
                            return None;
                        }
                        if let Some(x) = r.literal() {
                            lits.push(x.to_owned());
                        }
                    }
                }
                let any = or(lits.iter().map(|l| self.role(l)).collect());
                Some(if g.positive { any } else { not(any) })
            }
            GuardKind::AssertCall => {
                let Cond::Call { callee, .. } = &g.cond else {
                    return None;
                };
                let last = callee.rsplit('.').next().unwrap_or(callee);
                if self.guard_fns.contains(last) {
                    return Some(eq(var("owner"), var("principal")));
                }
                (GUARD_CALL.is_match(last) && self.mentions(&g.cond)).then(|| self.gate(&g.text))
            }
        }
    }
}

/// What Proof-It knows about a route middleware: its code (if it is in the
/// repository) decides what it can enforce; its name alone never does.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mw {
    /// Code found: what the body can actually do.
    Seen(GuardFact),
    /// Not in the repository (a library) or ambiguous: an opaque check.
    Unseen,
}

fn middleware_guard(ctx: &ExtractContext<'_>, route_module: &ModuleFacts, mw: &str) -> Mw {
    let base = mw.split('(').next().unwrap_or(mw).trim();
    let name = base.rsplit('.').next().unwrap_or(base);
    let candidates: Vec<(&ModuleFacts, GuardFact)> = ctx
        .facts
        .modules
        .iter()
        .flat_map(|mm| mm.functions.iter().filter_map(move |f| f.guard.filter(|_| f.name == name || f.name.rsplit('.').next() == Some(name)).map(|g| (mm, g))))
        .collect();
    let near: Vec<GuardFact> =
        candidates.iter().filter(|(mm, _)| mm.file == route_module.file || route_module.imports.contains(&mm.file)).map(|(_, g)| *g).collect();
    let pick = if near.is_empty() { candidates.iter().map(|(_, g)| *g).collect() } else { near };
    match pick.as_slice() {
        [g, rest @ ..] if rest.iter().all(|r| r == g) => Mw::Seen(*g),
        _ => Mw::Unseen,
    }
}

/// The exact roles a middleware admits (read from its code), when every
/// definition it could resolve to agrees; `None` when unknown.
fn middleware_admits(ctx: &ExtractContext<'_>, route_module: &ModuleFacts, mw: &str) -> Option<Vec<String>> {
    let (callee, call_args) = match mw.split_once('(') {
        Some((c, rest)) => (c, Some(rest.trim_end().strip_suffix(')')?)),
        None => (mw, None),
    };
    let name = callee.trim().rsplit('.').next().unwrap_or(callee).trim();
    let candidates: Vec<(&ModuleFacts, Option<Vec<String>>)> = ctx
        .facts
        .modules
        .iter()
        .flat_map(|mm| {
            mm.functions
                .iter()
                .filter(move |f| f.guard.is_some() && (f.name == name || f.name.rsplit('.').next() == Some(name)))
                .map(move |f| (mm, f.admits_roles.clone()))
        })
        .collect();
    let near: Vec<&Option<Vec<String>>> =
        candidates.iter().filter(|(mm, _)| mm.file == route_module.file || route_module.imports.contains(&mm.file)).map(|(_, r)| r).collect();
    let pick: Vec<&Option<Vec<String>>> = if near.is_empty() { candidates.iter().map(|(_, r)| r).collect() } else { near };
    let admits = match pick.as_slice() {
        [first, rest @ ..] if rest.iter().all(|r| r == first) => (*first).clone()?,
        _ => return None,
    };
    // Placeholders for a factory's parameters: the roles are the literals at the call
    // (`requireRole('admin', 'super_admin')`, `requireRole(['admin'])`); anything that
    // is not a plain string literal (a variable, a spread) leaves the set unknown.
    let literals = |s: &str| -> Option<Vec<String>> {
        let v: Option<Vec<String>> = s
            .split(',')
            .map(str::trim)
            .filter(|x| !x.is_empty())
            .map(|x| {
                let q = x.chars().next()?;
                (matches!(q, '\'' | '"') && x.len() >= 2 && x.ends_with(q) && !x[1..x.len() - 1].contains(['\'', '"', '\\']))
                    .then(|| x[1..x.len() - 1].to_owned())
            })
            .collect();
        v.filter(|v| !v.is_empty())
    };
    match (admits.as_slice(), call_args) {
        ([p], Some(args)) if p == "$args" => literals(args),
        ([p], Some(args)) if p == "$arg0" => literals(args.trim().strip_prefix('[')?.strip_suffix(']')?),
        (roles, _) if roles.iter().any(|r| r.starts_with('$')) => None,
        _ => Some(admits),
    }
}

/// Hypotheses and notes contributed by middleware: from what the code does,
/// falling back to an opaque gate (never a proof) when the code is not visible.
/// Returns (facts read from code, assumptions with their labels, notes).
fn middleware_hyps(env: &mut Env, ctx: &ExtractContext<'_>, m: &ModuleFacts, mws: &[String]) -> (Vec<Expr>, Vec<(Expr, String)>, Vec<String>) {
    let (mut hyps, mut assumed, mut notes) = (Vec::new(), Vec::new(), Vec::new());
    for mw in mws.iter().filter(|mw| !INFRA_MW.is_match(mw)) {
        let named_admin = ADMIN_MW.is_match(mw);
        let named_authz = AUTHZ_MW.is_match(mw);
        if !named_admin && !named_authz {
            continue;
        }
        match middleware_guard(ctx, m, mw) {
            Mw::Seen(g) if !g.can_deny => notes.push(format!("Middleware `{mw}` never denies a request (its code always continues): it enforces nothing.")),
            Mw::Seen(g) if named_admin && g.checks_role => {
                // Code evidence only when the exact set of roles the guard lets through
                // was read from its code and every one of them is a trusted admin role.
                // Naming an admin role somewhere in the body is not enough: a guard that
                // admits ['admin', 'user'] names 'admin' too.
                let a = env.is_admin();
                match middleware_admits(ctx, m, mw) {
                    Some(roles) if !roles.is_empty() && roles.iter().all(|r| env.admin_roles.contains(r)) => {
                        hyps.push(a);
                        notes.push(format!(
                            "Middleware `{mw}` denies unless role ∈ {{{}}} (read from its code), all of them admin roles ({}).",
                            roles.join(", "),
                            env.admin_roles.join(", ")
                        ));
                    }
                    Some(roles) => {
                        let others: Vec<&String> = roles.iter().filter(|r| !env.admin_roles.contains(r)).collect();
                        notes.push(format!(
                            "Middleware `{mw}` lets through role(s) that are not admin roles: {} (admin roles: {}). It is not an admin check.",
                            others.iter().map(|r| r.as_str()).collect::<Vec<_>>().join(", "),
                            env.admin_roles.join(", ")
                        ));
                    }
                    None => {
                        let note = format!(
                            "Middleware `{mw}` reads a role and can deny, but which roles it lets through could not be read from its code; that it requires role ∈ {{{}}} is assumed.",
                            env.admin_roles.join(", ")
                        );
                        assumed.push((a, note.clone()));
                        notes.push(note);
                    }
                }
            }
            Mw::Seen(_) if named_admin => {
                notes.push(format!("Middleware `{mw}` is named like an admin guard but reads no role or admin field: not treated as an admin check."));
            }
            Mw::Seen(_) => assumed.push((env.gate(&format!("middleware {mw}")), format!("middleware `{mw}` passes"))),
            Mw::Unseen => {
                assumed.push((env.gate(&format!("middleware {mw} (code not in the repository)")), format!("middleware `{mw}` passes")));
                notes.push(format!("Middleware `{mw}` is not in the repository: what it checks is unknown, so it cannot support a proof."));
            }
        }
    }
    (hyps, assumed, notes)
}

/// A middleware counts as authentication only if its code (when visible) can deny.
fn authenticates(ctx: &ExtractContext<'_>, m: &ModuleFacts, mw: &str) -> bool {
    (AUTH_MW.is_match(mw) || AUTHZ_MW.is_match(mw) || ADMIN_MW.is_match(mw)) && !matches!(middleware_guard(ctx, m, mw), Mw::Seen(g) if !g.can_deny)
}

/// The code-derived hypothesis, plus one `assumed` hypothesis when there are assumptions.
fn with_assumptions(code: Hypothesis, assumed: &[(Expr, String)]) -> Vec<Hypothesis> {
    let mut v = vec![code];
    if !assumed.is_empty() {
        v.push(Hypothesis {
            assumed: true,
            expr: and(assumed.iter().map(|(e, _)| e.clone()).collect()),
            label: format!("assumed: {}", assumed.iter().map(|(_, l)| l.as_str()).collect::<Vec<_>>().join("; ")),
            location: None,
        });
    }
    v
}

fn setup(h: &HandlerFact, ctx: &ExtractContext<'_>) -> Env {
    let a = &ctx.config.authorization;
    let p0 = h.params.first().map_or("req", |p| p.name.as_str()).to_owned();
    let mut principal_paths = BTreeSet::new();
    for p in &a.principal_paths {
        principal_paths.insert(p.clone());
        for (prefix, alt) in [("req.", "req"), ("ctx.", "ctx")] {
            if let Some(rest) = p.strip_prefix(prefix)
                && p0 != alt
            {
                principal_paths.insert(format!("{p0}.{rest}"));
            }
        }
    }
    let mut request_params = BTreeSet::new();
    for prm in &h.params {
        for d in &prm.decorators {
            match d.as_str() {
                "Param" | "Query" | "Body" | "Args" => {
                    request_params.insert(prm.name.clone());
                }
                // GraphQL context: the authenticated user is `context.user` (an id, or an object with one).
                "GqlContext" => {
                    for f in ["user.id", "user.sub", "user.userId", "user._id", "user"] {
                        principal_paths.insert(format!("{}.{f}", prm.name));
                    }
                }
                "User" | "CurrentUser" | "AuthUser" | "Principal" | "GetUser" | "ReqUser" => {
                    for f in ["id", "sub", "userId", "_id"] {
                        principal_paths.insert(format!("{}.{f}", prm.name));
                    }
                }
                "Req" | "Request" => {
                    for f in ["user.id", "user.sub", "user.userId"] {
                        principal_paths.insert(format!("{}.{f}", prm.name));
                    }
                }
                _ => {}
            }
        }
    }
    let principal_bases = principal_paths.iter().filter_map(|p| p.rsplit_once('.').map(|(b, _)| b.to_owned())).collect();
    let mut request_prefixes = Vec::new();
    for b in [p0.as_str(), "req", "request", "ctx.request", "ctx"] {
        for s in ["params", "query", "body"] {
            request_prefixes.push(format!("{b}.{s}."));
        }
    }
    Env {
        principal_paths,
        lookup_ids: BTreeSet::new(),
        tenant_scoped: Vec::new(),
        principal_bases,
        request_prefixes,
        request_params,
        resource: BTreeSet::new(),
        ownership: a.ownership_fields.iter().map(|f| f.to_ascii_lowercase()).collect(),
        admin_roles: proof_it_core::config::effective_admin_roles(ctx.config, ctx.org).0,
        guard_fns: a.guard_functions.iter().cloned().collect(),
        vars: BTreeMap::new(),
        role_members: vec![],
        gates: BTreeMap::new(),
        uses_role: false,
    }
}

struct SinkPath {
    sink: SinkFact,
    pc: Expr,
    steps: Vec<(Option<Expr>, String, SourceLocation)>,
}

fn paths_for(env: &mut Env, sinks: &[&SinkFact]) -> Vec<SinkPath> {
    sinks
        .iter()
        .map(|s| {
            let steps: Vec<(Option<Expr>, String, SourceLocation)> = s
                .guards
                .iter()
                .filter_map(|g| {
                    let e = env.guard_expr(g);
                    // Keep assertion calls in the trace only when they matter.
                    if g.kind == GuardKind::AssertCall && e.is_none() {
                        return None;
                    }
                    let text = match (g.positive, g.text.strip_prefix('!')) {
                        (true, _) => g.text.clone(),
                        (false, Some(inner)) if !inner.starts_with('=') => inner.trim_start_matches(['(', ' ']).trim_end_matches(')').to_owned(),
                        (false, _) => format!("!({})", g.text),
                    };
                    Some((e, text, g.location.clone()))
                })
                .collect();
            let pc = and(steps.iter().filter_map(|(e, _, _)| e.clone()).collect());
            SinkPath { sink: (*s).clone(), pc: if matches!(&pc, Expr::And { es } if es.is_empty()) { Expr::Bool { v: true } } else { pc }, steps }
        })
        .collect()
}

fn finish(env: &Env, with_identity: bool) -> (Vec<ModelVar>, Vec<EnumDecl>) {
    let mut vars = Vec::new();
    if with_identity {
        vars.push(ModelVar::new("principal", Sort::Nat, "id of the authenticated principal"));
        vars.push(ModelVar::new("owner", Sort::Nat, "owner id of the looked-up resource"));
    }
    let mut enums = Vec::new();
    if env.uses_role {
        let mut members = env.role_members.clone();
        if !members.iter().any(|m| m == "other") {
            members.push("other".into());
        }
        enums.push(EnumDecl { name: "Role".into(), members });
        vars.push(ModelVar::new("role", Sort::Enum { name: "Role".into() }, "role of the principal"));
    }
    vars.extend(env.vars.values().cloned());
    (vars, enums)
}

fn trace(h: &HandlerFact, paths: Vec<SinkPath>, lookups: Vec<LookupFact>, ids: Vec<String>, ob: Obligation, violated: &'static str) -> super::TraceFn {
    let method = h.method.clone();
    let path = h.path.clone();
    Arc::new(move |asg: &Assignment| {
        let ev = Evaluator::new(&ob);
        let chosen = paths.iter().find(|p| ev.holds(&p.pc, asg) == Ok(true)).or(paths.first());
        let show = |k: &str| {
            asg.get(k).map_or_else(
                || "?".to_owned(),
                |v| match v {
                    Value::Int(i) => i.to_string(),
                    Value::Bool(b) => b.to_string(),
                    Value::Sym(s) => s.clone(),
                },
            )
        };
        let mut steps = vec![CounterexampleStep::new(format!(
            "authenticate as principal {}{}",
            show("principal"),
            if asg.contains_key("role") { format!(" with role {}", show("role")) } else { String::new() }
        ))];
        for l in &lookups {
            steps.push(
                CounterexampleStep::new(format!("request {method} {path} with {} identifying a resource owned by {}", ids.join(", "), show("owner")))
                    .at(Some(l.location.clone())),
            );
            steps.push(CounterexampleStep::new(format!("handler looks up the resource: {}", l.text)).at(Some(l.location.clone())));
        }
        if let Some(p) = chosen {
            for (e, text, loc) in &p.steps {
                let outcome = match e {
                    None => "no effect on access (input validation / authentication)".to_owned(),
                    Some(x) => match ev.holds(x, asg) {
                        Ok(true) => "passes".into(),
                        Ok(false) => "fails".into(),
                        Err(_) => "unknown".into(),
                    },
                };
                steps.push(CounterexampleStep::new(format!("check {text} → {outcome}")).at(Some(loc.clone())));
            }
            let verb = if p.sink.kind == SinkKind::Write { "resource modified" } else { "response sent" };
            steps.push(CounterexampleStep::new(format!("{verb}: {}", p.sink.text)).at(Some(p.sink.location.clone())));
        }
        steps.push(CounterexampleStep::new(violated));
        steps
    })
}

pub fn extract(p: &Property, ctx: &ExtractContext<'_>) -> Vec<Extraction> {
    let admin_prop = p.spec.formal.as_ref().is_some_and(|f| f.extractor == Extractor::AuthzAdmin);
    let write_prop = p.spec.formal.as_ref().is_some_and(|f| f.extractor == Extractor::AuthzWrite);
    // Router mounts across files: prefixes and middleware that apply to each module's routes.
    let mut mounted: std::collections::HashMap<&str, Vec<(String, Vec<String>)>> = std::collections::HashMap::new();
    // Same-module path-scoped middleware: `app.use('/rest/basket', mw)` applies to `/rest/basket/...` routes.
    let mut scoped_mw: std::collections::HashMap<&str, Vec<(String, Vec<String>)>> = std::collections::HashMap::new();
    // Files that define routes: only those can be mounted as routers. An imported
    // last argument of `use(...)` that defines none is middleware for this module.
    let routers: std::collections::HashSet<&str> =
        ctx.facts.modules.iter().filter(|m| !m.routes.is_empty() || !m.route_refs.is_empty()).map(|m| m.file.as_str()).collect();
    for m in &ctx.facts.modules {
        for mt in &m.mounts {
            match &mt.target_module {
                Some(t) if routers.contains(t.as_str()) || mt.target_text.is_none() => {
                    mounted.entry(t.as_str()).or_default().push((mt.prefix.clone(), mt.middleware.clone()));
                }
                Some(_) => {
                    let mut mw = mt.middleware.clone();
                    mw.extend(mt.target_text.clone());
                    let into = if mt.prefix.is_empty() { &mut mounted } else { &mut scoped_mw };
                    into.entry(m.file.as_str()).or_default().push((mt.prefix.clone(), mw));
                }
                None if mt.prefix.is_empty() => mounted.entry(m.file.as_str()).or_default().push((String::new(), mt.middleware.clone())),
                None => scoped_mw.entry(m.file.as_str()).or_default().push((mt.prefix.clone(), mt.middleware.clone())),
            }
        }
    }
    // `/rest/basket/:id` matches route `/rest/basket/:id/checkout`; parameters match any segment.
    let path_has_prefix = |path: &str, prefix: &str| {
        let (p, q): (Vec<&str>, Vec<&str>) = (path.split('/').collect(), prefix.trim_end_matches('/').split('/').collect());
        q.len() <= p.len() && q.iter().zip(&p).all(|(a, b)| a == b || a.starts_with(':') || b.starts_with(':'))
    };
    let mut out = Vec::new();
    for m in &ctx.facts.modules {
        let mounts = mounted.get(m.file.as_str()).cloned().unwrap_or_default();
        let module_mw: Vec<String> = mounts.iter().filter(|(p, _)| p.is_empty()).flat_map(|(_, mw)| mw.clone()).collect();
        let prefixes: Vec<(String, Vec<String>)> = {
            let v: Vec<(String, Vec<String>)> = mounts.iter().filter(|(p, _)| !p.is_empty()).cloned().collect();
            if v.is_empty() { vec![(String::new(), vec![])] } else { v }
        };
        // Routes whose handler lives in another file: join by function name,
        // preferring modules this file imports, else a unique match.
        let mut all_handlers: Vec<HandlerFact> = m.handlers.clone();
        let resolve = |name: &str| -> Option<&HandlerFact> {
            let candidates: Vec<(&ModuleFacts, &HandlerFact)> = ctx
                .facts
                .modules
                .iter()
                .flat_map(|mm| mm.handler_bodies.iter().map(move |b| (mm, b)))
                .filter(|(_, b)| b.function == name || b.function.rsplit('.').next() == Some(name))
                .collect();
            let imported: Vec<&(&ModuleFacts, &HandlerFact)> = candidates.iter().filter(|(mm, _)| m.imports.contains(&mm.file)).collect();
            if imported.len() == 1 {
                Some(imported[0].1)
            } else if candidates.len() == 1 {
                Some(candidates[0].1)
            } else {
                None
            }
        };
        for r in &m.route_refs {
            // The handler is the first argument resolving to a handler body that responds;
            // middleware before it runs first; arguments after it run after the response.
            // Middleware (`(req, res, next)`) also responds (401s), so it is skipped unless
            // nothing else responds.
            let responds =
                |a: &RouteArg, allow_mw: bool| a.name.as_deref().and_then(resolve).is_some_and(|b| !b.sinks.is_empty() && (allow_mw || b.params.len() < 3));
            let idx = r.args.iter().position(|a| responds(a, false)).or_else(|| r.args.iter().position(|a| responds(a, true)));
            let (chosen, before, after): (Option<&HandlerFact>, Vec<String>, Vec<String>) = match idx {
                Some(i) => (
                    r.args[i].name.as_deref().and_then(resolve),
                    r.args[..i].iter().map(|a| a.text.clone()).collect(),
                    r.args[i + 1..].iter().map(|a| a.text.clone()).collect(),
                ),
                None => (resolve(&r.handler), r.middleware.clone(), vec![]),
            };
            if let Some(b) = chosen {
                let mut h = b.clone();
                h.defined_in = Some(b.location.file.clone());
                h.method.clone_from(&r.method);
                h.path.clone_from(&r.path);
                h.middleware = before;
                h.ineffective_middleware = after;
                h.location.clone_from(&r.location);
                all_handlers.push(h);
            }
        }
        // Middleware defined in the repository that overwrites request fields with server
        // data (e.g. `req.body.UserId = <token user>`): those fields identify the principal.
        let overrides_for = |mws: &[String]| -> Vec<String> {
            let mut out = Vec::new();
            for mw in mws {
                let name = mw.split('(').next().unwrap_or(mw).rsplit('.').next().unwrap_or(mw).trim();
                for mm in &ctx.facts.modules {
                    for f in mm.functions.iter().filter(|f| f.name == name || f.name.rsplit('.').next() == Some(name)) {
                        out.extend(f.request_overrides.iter().cloned());
                    }
                }
            }
            out
        };
        for (prefix, prefix_mw) in &prefixes {
            for h0 in &all_handlers {
                let mut hm = h0.clone();
                if !prefix.is_empty() {
                    hm.path = format!("{}{}", prefix.trim_end_matches('/'), if h0.path == "/" { "" } else { h0.path.as_str() });
                }
                let path_mw: Vec<String> = scoped_mw
                    .get(m.file.as_str())
                    .into_iter()
                    .flatten()
                    .filter(|(pre, _)| path_has_prefix(&h0.path, pre))
                    .flat_map(|(_, mw)| mw.clone())
                    .collect();
                hm.middleware = prefix_mw.iter().chain(module_mw.iter()).chain(path_mw.iter()).chain(h0.middleware.iter()).cloned().collect();
                let trusted = overrides_for(&hm.middleware);
                let h = &hm;
                let annotated = h.annotations.iter().any(|a| a == p.id());
                let target = format!("{} {} ({}:{})", h.method, h.path, h.location.file, h.location.line);
                let mut env = setup(h, ctx);
                for t in &trusted {
                    let p0 = h.params.first().map_or("req", |p| p.name.as_str()).to_owned();
                    for path in [t.clone(), t.replacen("req.", &format!("{p0}."), 1)] {
                        env.principal_paths.insert(path);
                    }
                }
                let mut assumptions = p.spec.assumptions.clone();
                assumptions.extend(
                    h.middleware
                        .iter()
                        .filter(|mw| !INFRA_MW.is_match(mw))
                        .map(|mw| format!("Route middleware `{mw}` runs before the handler (its body is not analysed).")),
                );
                let ineffective_note: Vec<String> = h
                    .ineffective_middleware
                    .iter()
                    .filter(|mw| AUTHZ_MW.is_match(mw) || ADMIN_MW.is_match(mw) || AUTH_MW.is_match(mw) || mw.contains("check") || mw.contains("guard"))
                    .map(|mw| format!("`{mw}` is registered AFTER the handler: it runs after the response is sent and protects nothing."))
                    .collect();
                let mut hyps: Vec<Expr> = Vec::new();
                // Assumptions (not read from code), kept apart so a result that follows
                // from them alone is never reported as PROVEN.
                let mut assumed: Vec<(Expr, String)> = Vec::new();
                let mut summary = Vec::new();
                if !admin_prop {
                    let lookups: Vec<LookupFact> = h.lookups.iter().filter(|l| l.arg_paths.iter().any(|a| env.is_request_id(a))).cloned().collect();
                    if lookups.is_empty() && !annotated {
                        continue;
                    }
                    let authenticated = h.middleware.iter().filter(|mw| !INFRA_MW.is_match(mw)).any(|mw| authenticates(ctx, m, mw))
                        || h.body_paths.iter().any(|bp| env.principal_bases.iter().any(|b| bp == b || bp.starts_with(&format!("{b}."))));
                    // A guard the developer attached that turns out to enforce nothing shows the
                    // route was meant to be protected: analyse it instead of treating it as public.
                    let intended_guard = h.middleware.iter().any(|mw| {
                        (AUTH_MW.is_match(mw) || AUTHZ_MW.is_match(mw) || ADMIN_MW.is_match(mw))
                            && matches!(middleware_guard(ctx, m, mw), Mw::Seen(g) if !g.can_deny)
                    });
                    if !authenticated && !annotated && !intended_guard {
                        continue;
                    }
                    for l in &lookups {
                        env.resource.extend(l.names.iter().cloned());
                        let ids: Vec<String> = l.arg_paths.iter().filter(|a| env.is_request_id(a)).cloned().collect();
                        env.lookup_ids.extend(ids);
                    }
                    for _ in 0..4 {
                        for (a, b) in &h.derived {
                            if env.resource.contains(b) {
                                env.resource.insert(a.clone());
                            }
                        }
                    }
                    let sinks: Vec<&SinkFact> = h
                        .sinks
                        .iter()
                        .filter(|s| (s.kind == SinkKind::Write) == write_prop)
                        .filter(|s| !s.error_status && s.refs.iter().any(|r| env.resource.contains(r)) && (s.kind != SinkKind::Return || !h.has_response_param))
                        .collect();
                    if sinks.is_empty() {
                        continue;
                    }
                    let mut ids: Vec<String> = Vec::new();
                    for l in &lookups {
                        let scoped = l.arg_paths.iter().any(|a| env.principal_paths.contains(a));
                        let req_ids: Vec<String> = l.arg_paths.iter().filter(|a| env.is_request_id(a)).cloned().collect::<BTreeSet<_>>().into_iter().collect();
                        ids.extend(req_ids.iter().cloned());
                        if scoped {
                            hyps.push(eq(var("owner"), var("principal")));
                            let note = format!(
                                "Lookup `{}` filters by the principal; assumed to return only resources owned by the principal (data-layer semantics).",
                                l.text
                            );
                            summary.push(note.clone());
                            assumptions.push(note);
                        } else {
                            for id in &req_ids {
                                let last = id.rsplit('.').next().unwrap_or("").to_ascii_lowercase();
                                if env.ownership.contains(&last) {
                                    let rv = env.request_var(id);
                                    let note = format!("Lookup by `{id}` assumed to return resources owned by that id.");
                                    assumed.push((eq(var("owner"), var(&rv)), note.clone()));
                                    summary.push(note.clone());
                                    assumptions.push(note);
                                }
                            }
                        }
                    }
                    let (mh, ah, notes) = middleware_hyps(&mut env, ctx, m, &h.middleware);
                    hyps.extend(mh);
                    assumed.extend(ah);
                    summary.extend(notes.iter().cloned());
                    assumptions.extend(notes);
                    let paths = paths_for(&mut env, &sinks);
                    for t in &env.tenant_scoped {
                        let note = format!("Tenant scoping `{t}`: a resource looked up by the principal's own tenant id is treated as owned by the principal.");
                        if !assumptions.contains(&note) {
                            assumptions.push(note.clone());
                            summary.push(note);
                        }
                    }
                    let concl = if env.admin_roles.is_empty() {
                        eq(var("owner"), var("principal"))
                    } else {
                        let a = env.is_admin();
                        or(vec![eq(var("owner"), var("principal")), a])
                    };
                    let (vars, enums) = finish(&env, true);
                    if !env.guard_fns.is_empty() {
                        assumptions.push(format!(
                            "Configured guard functions ({}) enforce ownership (declared, not verified).",
                            env.guard_fns.iter().cloned().collect::<Vec<_>>().join(", ")
                        ));
                    }
                    summary.insert(
                        0,
                        format!(
                            "Handler {} {}: {} lookup(s) by client-supplied id, {} response(s) containing the resource.",
                            h.method,
                            h.path,
                            lookups.len(),
                            sinks.len()
                        ),
                    );
                    summary.extend(ineffective_note.iter().cloned());
                    assumptions.extend(ineffective_note.iter().cloned());
                    if !env.gates.is_empty() {
                        summary.push(format!("{} check(s) could not be interpreted and are modeled as opaque conditions.", env.gates.len()));
                    }
                    let mut hyp_all = hyps.clone();
                    hyp_all.push(or(paths.iter().map(|x| x.pc.clone()).collect()));
                    let ob = Obligation {
                        theorem: format!("{}_{}_{}", p.spec.formal.as_ref().map_or("isolation", |f| f.theorem.as_str()), h.method, h.path),
                        property_id: p.id().to_owned(),
                        statement: format!(
                            "If {} {} {} the resource identified by the client, then the principal owns it{}.",
                            h.method,
                            h.path,
                            if write_prop { "modifies or deletes" } else { "sends to the client" },
                            if env.admin_roles.is_empty() { String::new() } else { format!(" or has role {}", env.admin_roles.join("/")) }
                        ),
                        enums,
                        defs: vec![],
                        vars,
                        hypotheses: with_assumptions(
                            Hypothesis {
                                assumed: false,
                                expr: and(hyp_all),
                                label: if write_prop {
                                    "the handler modifies the resource".into()
                                } else {
                                    "the handler reaches a response containing the resource".into()
                                },
                                location: sinks.first().map(|s| s.location.clone()),
                            },
                            &assumed,
                        ),
                        conclusion: concl,
                        extras: vec![],
                        meaningful_if: None,
                    };
                    let tr = trace(
                        h,
                        paths,
                        lookups,
                        ids,
                        ob.clone(),
                        if write_prop {
                            "property violated: a resource owned by another user was modified"
                        } else {
                            "property violated: a resource owned by another user was returned"
                        },
                    );
                    out.push(Extraction {
                        property_id: p.id().to_owned(),
                        target,
                        location: Some(h.location.clone()),
                        obligation: Some(ob),
                        status: None,
                        reason: None,
                        assumptions,
                        spec_source: p.source,
                        trace: Some(tr),
                        replay: None,
                        model_summary: summary,
                        files: std::iter::once(h.location.file.clone()).chain(h.defined_in.clone()).collect(),
                    });
                } else {
                    let admin_path = h.path.split('/').any(|seg| seg.eq_ignore_ascii_case("admin"));
                    if !admin_path && !annotated {
                        continue;
                    }
                    env.uses_role = true;
                    let (mh, ah, notes) = middleware_hyps(&mut env, ctx, m, &h.middleware);
                    hyps.extend(mh);
                    assumed.extend(ah);
                    summary.extend(notes.iter().cloned());
                    assumptions.extend(notes);
                    let sinks: Vec<&SinkFact> = h.sinks.iter().filter(|s| !s.error_status && (s.kind != SinkKind::Return || !h.has_response_param)).collect();
                    let paths = if sinks.is_empty() {
                        vec![SinkPath {
                            sink: SinkFact {
                                kind: SinkKind::Return,
                                refs: vec![],
                                error_status: false,
                                text: "(end of handler)".into(),
                                location: h.location.clone(),
                                guards: vec![],
                            },
                            pc: Expr::Bool { v: true },
                            steps: vec![],
                        }]
                    } else {
                        paths_for(&mut env, &sinks)
                    };
                    let concl = env.is_admin();
                    let (vars, enums) = finish(&env, false);
                    summary.push(format!("Admin handler {} {}: {} successful response(s).", h.method, h.path, paths.len()));
                    let mut hyp_all = hyps.clone();
                    hyp_all.push(or(paths.iter().map(|x| x.pc.clone()).collect()));
                    let mut used = Vec::new();
                    and(hyp_all.clone()).vars(&mut used);
                    for (a, _) in &assumed {
                        a.vars(&mut used);
                    }
                    concl.vars(&mut used);
                    let ob = Obligation {
                        theorem: format!("non_admin_cannot_call_{}_{}", h.method, h.path),
                        property_id: p.id().to_owned(),
                        statement: format!("{} {} responds successfully only when the principal has role {}.", h.method, h.path, env.admin_roles.join("/")),
                        enums,
                        defs: vec![],
                        vars: vars.into_iter().filter(|v| used.contains(&v.name)).collect(),
                        hypotheses: with_assumptions(
                            Hypothesis {
                                assumed: false,
                                expr: and(hyp_all),
                                label: "the handler reaches a successful response".into(),
                                location: paths.first().map(|s| s.sink.location.clone()),
                            },
                            &assumed,
                        ),
                        conclusion: concl,
                        extras: vec![],
                        meaningful_if: None,
                    };
                    let tr = trace(h, paths, vec![], vec![], ob.clone(), "property violated: a non-admin principal reached a successful admin response");
                    out.push(Extraction {
                        property_id: p.id().to_owned(),
                        target,
                        location: Some(h.location.clone()),
                        obligation: Some(ob),
                        status: None,
                        reason: None,
                        assumptions,
                        spec_source: p.source,
                        trace: Some(tr),
                        replay: None,
                        model_summary: summary,
                        files: std::iter::once(h.location.file.clone()).chain(h.defined_in.clone()).collect(),
                    });
                }
            }
        }
    }
    out
}
