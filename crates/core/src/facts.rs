//! Language-neutral program facts.
//!
//! Language adapters (crates/lang-*) turn source files into these owned facts;
//! the formal extractors (crates/model) consume only facts. Adding a language
//! therefore means writing an adapter that produces facts — every formal
//! property then works for it unchanged.
//!
//! Facts are deliberately *syntactic summaries with guards*: for each
//! interesting program point (a state write, a response that sends a resource,
//! a balance update) the adapter records the conditions that must hold for
//! control to reach it. Access paths are normalised (`a?.b` → `a.b`) and local
//! aliases are resolved (`const s = e.status; if (s === "A")` → `e.status`).

use crate::types::{Finding, SourceLocation};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Language {
    Typescript,
    Javascript,
    Python,
    Go,
    Rust,
}

impl Language {
    pub fn name(self) -> &'static str {
        match self {
            Self::Typescript => "typescript",
            Self::Javascript => "javascript",
            Self::Python => "python",
            Self::Go => "go",
            Self::Rust => "rust",
        }
    }
    /// Languages Proof-It has an analyser for. Source files in any other
    /// recognised language are reported as not analysed (never silently skipped).
    pub fn is_supported(self) -> bool {
        matches!(self, Self::Typescript | Self::Javascript | Self::Go)
    }
    pub fn from_extension(ext: &str) -> Option<Self> {
        match ext {
            "ts" | "tsx" | "mts" | "cts" => Some(Self::Typescript),
            "js" | "jsx" | "mjs" | "cjs" => Some(Self::Javascript),
            "py" => Some(Self::Python),
            "go" => Some(Self::Go),
            "rs" => Some(Self::Rust),
            _ => None,
        }
    }
}

/// A value expression as it appears in source, reduced to what extractors need.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "k", rename_all = "snake_case")]
pub enum Val {
    /// Normalised, alias-resolved access path: `req.user.id`, `e.status`, `amount`.
    Path {
        path: String,
    },
    Str {
        v: String,
    },
    Int {
        v: i64,
    },
    /// Non-integer numeric literal (kept textual: floats are not modeled).
    Float {
        text: String,
    },
    Bool {
        v: bool,
    },
    Null,
    Undefined,
    /// `x.length`
    Len {
        path: String,
    },
    Bin {
        op: ArithOp,
        l: Box<Val>,
        r: Box<Val>,
    },
    Neg {
        e: Box<Val>,
    },
    /// `Enum.Member` reference (value = member name)
    EnumMember {
        enum_name: String,
        member: String,
    },
    Call {
        callee: String,
        args: Vec<Val>,
    },
    /// Anything else; `paths` lists the access paths it mentions.
    Other {
        text: String,
        paths: Vec<String>,
    },
}

impl Val {
    /// Access paths mentioned anywhere inside.
    pub fn paths(&self, out: &mut Vec<String>) {
        match self {
            Val::Path { path } | Val::Len { path } => out.push(path.clone()),
            Val::Bin { l, r, .. } => {
                l.paths(out);
                r.paths(out);
            }
            Val::Neg { e } => e.paths(out),
            Val::Call { args, .. } => args.iter().for_each(|a| a.paths(out)),
            Val::Other { paths, .. } => out.extend(paths.iter().cloned()),
            _ => {}
        }
    }
    /// String-ish literal value (string literal or enum member).
    pub fn literal(&self) -> Option<&str> {
        match self {
            Val::Str { v } => Some(v),
            Val::EnumMember { member, .. } => Some(member),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl CmpOp {
    pub fn negate(self) -> Self {
        match self {
            Self::Eq => Self::Ne,
            Self::Ne => Self::Eq,
            Self::Lt => Self::Ge,
            Self::Le => Self::Gt,
            Self::Gt => Self::Le,
            Self::Ge => Self::Lt,
        }
    }
}

/// A boolean condition from source.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "k", rename_all = "snake_case")]
pub enum Cond {
    Not {
        c: Box<Cond>,
    },
    And {
        cs: Vec<Cond>,
    },
    Or {
        cs: Vec<Cond>,
    },
    Cmp {
        op: CmpOp,
        l: Val,
        r: Val,
    },
    /// `x` used as a boolean.
    Truthy {
        v: Val,
    },
    /// `[A, B].includes(x)`
    InList {
        list: Vec<String>,
        item: Val,
    },
    /// `TABLE[key].includes(item)`
    TableHas {
        table: String,
        key: Val,
        item: Val,
    },
    /// A call used as a boolean, or an assertion-style statement call.
    Call {
        callee: String,
        args: Vec<Val>,
        text: String,
    },
    Other {
        text: String,
        paths: Vec<String>,
    },
}

impl Cond {
    pub fn paths(&self, out: &mut Vec<String>) {
        match self {
            Cond::Not { c } => c.paths(out),
            Cond::And { cs } | Cond::Or { cs } => cs.iter().for_each(|c| c.paths(out)),
            Cond::Cmp { l, r, .. } => {
                l.paths(out);
                r.paths(out);
            }
            Cond::Truthy { v } => v.paths(out),
            Cond::InList { item, .. } => item.paths(out),
            Cond::TableHas { key, item, .. } => {
                key.paths(out);
                item.paths(out);
            }
            Cond::Call { args, .. } => args.iter().for_each(|a| a.paths(out)),
            Cond::Other { paths, .. } => out.extend(paths.iter().cloned()),
        }
    }
    pub fn all_paths(&self) -> Vec<String> {
        let mut v = Vec::new();
        self.paths(&mut v);
        v
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GuardKind {
    /// Inside the then/else branch of an `if`, ternary, `&&`/`||`.
    Branch,
    /// After `if (c) <exit>` in the same or an enclosing block.
    EarlyExit,
    /// Inside a `switch` case (cond is the case selection).
    Case,
    /// After a standalone call statement (assertion-style guard).
    AssertCall,
}

/// A condition that holds (if `positive`) or fails (if not) on the path to a program point.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Guard {
    pub kind: GuardKind,
    pub cond: Cond,
    pub positive: bool,
    /// Source text of the condition, for traces.
    pub text: String,
    pub location: SourceLocation,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionFact {
    pub name: String,
    pub params: Vec<String>,
    pub location: SourceLocation,
    pub exported: bool,
    pub is_async: bool,
    pub statements: usize,
    /// Explicit property bindings from `@proof-it AUTHZ-001` doc tags.
    pub annotations: Vec<String>,
    /// Request fields this function overwrites from non-request data
    /// (middleware like `req.body.UserId = token.user.id`), as `req.body.UserId`.
    #[serde(default)]
    pub request_overrides: Vec<String>,
    /// For `(req, res, next)` middleware: what its body can actually do.
    #[serde(default)]
    pub guard: Option<GuardFact>,
    /// For middleware: the exact set of roles it lets through, when that can be
    /// read from the code (see `lang-ts` `admitted_roles`); `None` when it cannot.
    #[serde(default)]
    pub admits_roles: Option<Vec<String>>,
}

/// What a middleware body does, read from its code (not its name).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct GuardFact {
    /// Some path denies the request: an error status (>= 400), a redirect, a
    /// throw, or `next(err)`. Without one the middleware protects nothing.
    pub can_deny: bool,
    /// Reads a role / admin / permission field or names an admin role.
    pub checks_role: bool,
    /// Verifies an identity: token verification, `req.user`, session, Authorization header.
    pub checks_identity: bool,
    /// Names an admin role literally (`'admin'`, `'super_admin'`, ...).
    #[serde(default)]
    pub names_admin: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnumFact {
    pub name: String,
    pub members: Vec<String>,
    pub location: SourceLocation,
    pub kind: EnumKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum EnumKind {
    Enum,
    Union,
    ConstObject,
}

/// `const ALLOWED = { A: ["B"], B: [] }`
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransitionTableFact {
    pub name: String,
    pub edges: Vec<(String, String)>,
    pub location: SourceLocation,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "k", rename_all = "snake_case")]
pub enum WriteValue {
    /// One of these literals (a ternary of literals gives several).
    Lits {
        values: Vec<String>,
    },
    /// A local identifier (possibly a parameter).
    Ident {
        name: String,
    },
    /// A query/statement parameter (`$1`, `?`).
    QueryParam,
    Other {
        text: String,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum WriteKind {
    Assignment,
    OrmUpdate,
    Sql,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "k", rename_all = "snake_case")]
pub enum WhereStates {
    In { values: Vec<String> },
    NotIn { values: Vec<String> },
}

/// A write to a state-like field.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateWriteFact {
    pub kind: WriteKind,
    pub field: String,
    /// Receiver access path for assignments (`emergency`), None for ORM/SQL writes.
    pub receiver: Option<String>,
    /// Entity name (`emergency`), from the receiver, ORM model or SQL table.
    pub entity: String,
    pub value: WriteValue,
    /// ORM/SQL where-clause constraint on the current state.
    pub where_states: Option<WhereStates>,
    pub guards: Vec<Guard>,
    /// Initialisation (constructor, freshly created object, insert) — not a transition.
    pub init: bool,
    pub function: String,
    pub function_params: Vec<String>,
    pub function_exported: bool,
    pub location: SourceLocation,
    /// String literals compared against the subject anywhere in the function.
    pub compared_literals: Vec<String>,
    /// Declared type of the written value when it is a typed parameter (`next: Status`).
    #[serde(default)]
    pub value_type: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParamFact {
    pub name: String,
    /// Decorator names (`Param`, `Body`, `User`, `Req`, ...).
    pub decorators: Vec<String>,
}

/// `const record = await db.find(req.params.id)`
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LookupFact {
    /// Bound names (destructuring gives several).
    pub names: Vec<String>,
    /// Alias-resolved access paths used in the call arguments.
    pub arg_paths: Vec<String>,
    pub text: String,
    pub location: SourceLocation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SinkKind {
    /// `res.json(x)`, `res.send(x)`, `reply.send(x)`
    Response,
    /// `return x` from a handler without a response object
    Return,
    /// `ctx.body = x`
    ContextBody,
    /// A modification of the resource: `record.save()`, `Model.update({ where: { id } })`.
    Write,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SinkFact {
    pub kind: SinkKind,
    /// Identifiers referenced in the sent value.
    pub refs: Vec<String>,
    /// The response explicitly uses a 4xx/5xx status.
    pub error_status: bool,
    pub text: String,
    pub location: SourceLocation,
    pub guards: Vec<Guard>,
}

/// An HTTP handler (route registration or framework decorator).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HandlerFact {
    pub method: String,
    pub path: String,
    pub middleware: Vec<String>,
    pub location: SourceLocation,
    pub function: String,
    pub params: Vec<ParamFact>,
    pub annotations: Vec<String>,
    pub lookups: Vec<LookupFact>,
    /// (a, b) for every local `a` whose initialiser references identifier `b`.
    pub derived: Vec<(String, String)>,
    pub sinks: Vec<SinkFact>,
    /// Every alias-resolved access path mentioned in the body.
    pub body_paths: Vec<String>,
    pub has_response_param: bool,
    /// File defining the handler body when it differs from the registration file.
    #[serde(default)]
    pub defined_in: Option<String>,
    /// Middleware registered AFTER the handler (runs after the response; protects nothing).
    #[serde(default)]
    pub ineffective_middleware: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AssignOp {
    Set,
    Add,
    Sub,
}

/// One statement of a function that updates balances, in order.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "k", rename_all = "snake_case")]
pub enum LedgerStmt {
    Let {
        name: String,
        value: Val,
        location: SourceLocation,
    },
    BalanceWrite {
        receiver: String,
        field: String,
        op: AssignOp,
        value: Val,
        text: String,
        location: SourceLocation,
    },
    /// `if (cond) <exit>` with no else: `cond` is false afterwards.
    ExitGuard {
        cond: Cond,
        text: String,
        location: SourceLocation,
    },
    /// A construct outside the supported fragment that touches a balance.
    Unsupported {
        reason: String,
        location: SourceLocation,
    },
    Return {
        location: SourceLocation,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LedgerFunctionFact {
    pub name: String,
    pub params: Vec<String>,
    pub exported: bool,
    pub is_async: bool,
    pub location: SourceLocation,
    pub stmts: Vec<LedgerStmt>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RouteFact {
    pub method: String,
    pub path: String,
    pub handler: String,
    pub location: SourceLocation,
}

/// One argument of a route registration, in order.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RouteArg {
    pub text: String,
    /// Function name it refers to (`controller.show` → `show`), if any.
    pub name: Option<String>,
}

/// A route registered with a handler defined elsewhere (`app.get("/x", mw, handlers.show)`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RouteRefFact {
    pub method: String,
    pub path: String,
    pub middleware: Vec<String>,
    pub location: SourceLocation,
    /// Simple name of the referenced handler function (the last argument).
    pub handler: String,
    /// All arguments in order: the handler is the first one that resolves to a
    /// handler body; arguments after it run after the response and protect nothing.
    #[serde(default)]
    pub args: Vec<RouteArg>,
}

/// `app.use("/admin", mw, adminRouter)` or a module-level `router.use(mw)`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MountFact {
    pub prefix: String,
    pub middleware: Vec<String>,
    /// Repository path of the mounted router module (resolved import), if known.
    /// `None` = middleware applied to this module's own routes (all of them when the
    /// prefix is empty, otherwise those whose path starts with the prefix).
    pub target_module: Option<String>,
    /// Source text of the mounted argument when `target_module` is set. An imported
    /// name is not necessarily a router: `router.use(auth, adminMiddleware)` mounts
    /// imported middleware, which the model recognises because that file has no routes.
    #[serde(default)]
    pub target_text: Option<String>,
    pub location: SourceLocation,
}

/// Everything an adapter learned about one file.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleFacts {
    pub file: String,
    pub language: Language,
    pub functions: Vec<FunctionFact>,
    pub routes: Vec<RouteFact>,
    pub enums: Vec<EnumFact>,
    pub tables: Vec<TransitionTableFact>,
    pub state_writes: Vec<StateWriteFact>,
    pub handlers: Vec<HandlerFact>,
    pub ledger_functions: Vec<LedgerFunctionFact>,
    /// Repository-relative paths of imported local modules (for the import graph).
    pub imports: Vec<String>,
    #[serde(default)]
    pub mounts: Vec<MountFact>,
    /// Bodies of request-handler-shaped functions (`(req, res) => …`), keyed by function name,
    /// for routes registered in other files.
    #[serde(default)]
    pub handler_bodies: Vec<HandlerFact>,
    #[serde(default)]
    pub route_refs: Vec<RouteRefFact>,
    /// SHA-256 of the source text.
    pub hash: String,
}

/// Adapter output for one file: facts plus language-specific findings
/// (security, static checks).
#[derive(Debug, Clone)]
pub struct ModuleAnalysis {
    pub facts: ModuleFacts,
    pub findings: Vec<Finding>,
    /// The source text, kept for applicability signals.
    pub text: String,
}

#[derive(Debug, Clone, Default)]
pub struct ProgramFacts {
    pub modules: Vec<ModuleFacts>,
    pub texts: Vec<(String, String)>,
    pub parse_errors: Vec<(String, String)>,
}

impl ProgramFacts {
    pub fn function_count(&self) -> usize {
        self.modules.iter().map(|m| m.functions.len()).sum()
    }
}

/// A small source edit that injects a known bug class (mutation testing).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Mutant {
    pub id: String,
    pub operator: String,
    pub location: SourceLocation,
    pub description: String,
    pub start: usize,
    pub end: usize,
    pub replacement: String,
}

impl Mutant {
    pub fn apply(&self, text: &str) -> Option<String> {
        if self.start > self.end || self.end > text.len() || !text.is_char_boundary(self.start) || !text.is_char_boundary(self.end) {
            return None;
        }
        Some(format!("{}{}{}", &text[..self.start], self.replacement, &text[self.end..]))
    }
}
