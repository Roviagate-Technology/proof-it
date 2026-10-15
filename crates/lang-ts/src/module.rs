//! Per-file analysis: two passes over the oxc AST.
//!
//! Pass 1 collects declarations that later passes need: function names (by
//! span), exported names, enums/unions, transition tables, imports, route and
//! NestJS handler registrations, `@proof-it` annotations.
//! Pass 2 visits every function and runs the guarded walker, producing
//! function, state-write, handler and ledger facts.

use crate::expr::{Aliases, Conv, collect_aliases, inner, lit_str};
use crate::text::{Source, collapse};
use crate::walker::{FnInfo, Walker, exits, idents};
use oxc::ast::Comment;
use oxc::ast::ast::*;
use oxc::ast_visit::{Visit, walk};
use oxc::span::{GetSpan, Span};
use oxc::syntax::operator::{AssignmentOperator, UpdateOperator};
use oxc::syntax::scope::ScopeFlags;
use proof_it_core::facts::Language as Lang;
use proof_it_core::facts::*;
use regex::Regex;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::LazyLock;

static BALANCE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"(?i)^(balance|balanceCents|availableBalance|funds|credits|walletBalance|amountAvailable)$").expect("static regex"));
const HTTP_METHODS: [&str; 6] = ["get", "post", "put", "patch", "delete", "all"];
const NEST_METHODS: [&str; 6] = ["Get", "Post", "Put", "Patch", "Delete", "All"];

/// A function-like node: declaration/expression or arrow.
#[derive(Clone, Copy)]
pub enum FnRef<'x, 'a> {
    Func(&'x Function<'a>),
    Arrow(&'x ArrowFunctionExpression<'a>),
}

impl<'x, 'a> FnRef<'x, 'a> {
    pub fn span(&self) -> Span {
        match self {
            Self::Func(f) => f.span,
            Self::Arrow(a) => a.span,
        }
    }
    pub fn params(&self) -> &'x FormalParameters<'a> {
        match self {
            Self::Func(f) => &f.params,
            Self::Arrow(a) => &a.params,
        }
    }
    pub fn statements(&self) -> Option<&'x [Statement<'a>]> {
        match self {
            Self::Func(f) => f.body.as_ref().map(|b| b.statements.as_slice()),
            Self::Arrow(a) => match &a.body {
                ArrowFunctionBody::FunctionBody(b) => Some(b.statements.as_slice()),
                _ => None,
            },
        }
    }
    pub fn expression_body(&self) -> Option<&'x Expression<'a>> {
        match self {
            Self::Arrow(a) => a.body.as_expression(),
            Self::Func(_) => None,
        }
    }
    pub fn is_async(&self) -> bool {
        match self {
            Self::Func(f) => f.r#async,
            Self::Arrow(a) => a.r#async,
        }
    }
}

/// Simple type names of parameter annotations (`x: Status` → Some("Status")).
pub fn param_types(p: &FormalParameters<'_>, src: &Source<'_>) -> Vec<Option<String>> {
    p.items
        .iter()
        .map(|i| {
            let t = i.type_annotation.as_ref()?;
            let text = src.slice(t.type_annotation.span()).trim().to_owned();
            text.chars().all(|c| c.is_alphanumeric() || c == '_' || c == '$').then_some(text)
        })
        .collect()
}

pub fn param_names(p: &FormalParameters<'_>) -> Vec<String> {
    p.items.iter().map(|i| i.pattern.get_identifier_name().map_or_else(|| "_".to_owned(), |n| n.as_str().to_owned())).collect()
}

/// Parameters of a function that returns middleware: the first named one and the
/// rest parameter, the only two whose call-site arguments `admitted_roles` maps.
#[derive(Debug, Clone, Default)]
struct FactoryParams {
    first: Option<String>,
    rest: Option<String>,
}

/// A `use(...)` call: (prefix, middleware, mounted (import binding, source text), location).
type RawMount = (String, Vec<String>, Option<(String, String)>, proof_it_core::types::SourceLocation);

#[derive(Debug, Clone)]
struct FnMeta {
    name: String,
    /// Offset of the enclosing statement (for doc comments).
    stmt_start: u32,
    class: Option<String>,
    is_constructor: bool,
}

#[derive(Debug, Clone)]
enum HandlerTarget {
    Span(u32),
    Name(String),
}

#[derive(Debug, Clone)]
struct HandlerReg {
    method: String,
    path: String,
    middleware: Vec<String>,
    location: proof_it_core::types::SourceLocation,
    target: HandlerTarget,
    /// All arguments in registration order (for handlers resolved by name across files).
    args: Vec<RouteArg>,
}

#[derive(Default)]
struct Pass1 {
    meta: HashMap<u32, FnMeta>,
    exported: HashSet<String>,
    exported_classes: HashSet<String>,
    enums: Vec<EnumFact>,
    tables: Vec<TransitionTableFact>,
    imports: BTreeSet<String>,
    routes: Vec<RouteFact>,
    handlers: Vec<HandlerReg>,
    /// local binding → import specifier
    import_bindings: HashMap<String, String>,
    /// (prefix, middleware, mounted identifier or None for module-wide use, location)
    mounts: Vec<RawMount>,
    /// Functions returned by a factory (`const f = (...roles) => (req, res, next) => …`):
    /// span start of the returned function → the factory's parameters.
    factory_params: HashMap<u32, FactoryParams>,
    class_stack: Vec<(String, String, Vec<String>)>, // (name, controller prefix, guards)
}

struct P1<'c, 's> {
    src: &'c Source<'s>,
    st: Pass1,
    stmt_start: u32,
}

/// `router.route("/p")` (possibly followed by other verb calls): the route path.
static GRAPHQL_FILE: LazyLock<Regex> = LazyLock::new(|| {
    #[allow(clippy::expect_used)]
    Regex::new(r"(?i)graphql|apollo|typeDefs|\bgql`").expect("static regex")
});

fn route_chain_path(e: &Expression<'_>) -> Option<String> {
    match inner(e) {
        Expression::CallExpression(c) => {
            let m = c.callee.get_inner_expression().as_member_expression()?;
            if m.static_property_name()? == "route" {
                c.arguments.first().and_then(|a| a.as_expression()).and_then(lit_str).filter(|p| p.starts_with('/')).map(str::to_owned)
            } else {
                route_chain_path(m.object())
            }
        }
        _ => None,
    }
}

/// Resolve the handler of a route registration, unwrapping wrappers and factories:
/// `h`, `ctrl.h`, `(req, res) => …`, `asyncHandler(h)`, `asyncHandler(factory())`, `factory()`.
fn handler_target(e: &Expression<'_>) -> Option<HandlerTarget> {
    match inner(e) {
        Expression::ArrowFunctionExpression(a) => Some(HandlerTarget::Span(a.span.start)),
        Expression::FunctionExpression(f) => Some(HandlerTarget::Span(f.span.start)),
        Expression::Identifier(id) => Some(HandlerTarget::Name(id.name.as_str().to_owned())),
        Expression::StaticMemberExpression(sm) => Some(HandlerTarget::Name(sm.property.name.as_str().to_owned())),
        Expression::CallExpression(w) => match w.arguments.first().and_then(|a| a.as_expression()) {
            Some(arg) => handler_target(arg),
            None => match inner(&w.callee) {
                Expression::Identifier(id) => Some(HandlerTarget::Name(id.name.as_str().to_owned())),
                Expression::StaticMemberExpression(sm) => Some(HandlerTarget::Name(sm.property.name.as_str().to_owned())),
                _ => None,
            },
        },
        _ => None,
    }
}

fn literal_member(e: &Expression<'_>) -> Option<String> {
    match inner(e) {
        Expression::StringLiteral(s) => Some(s.value.as_str().to_owned()),
        Expression::StaticMemberExpression(m) if matches!(inner(&m.object), Expression::Identifier(id) if id.name.as_str().starts_with(char::is_uppercase)) => {
            Some(m.property.name.as_str().to_owned())
        }
        _ => None,
    }
}

fn decorator_name(d: &Decorator<'_>, src: &Source<'_>) -> (String, Vec<String>) {
    match &d.expression {
        Expression::CallExpression(c) => (src.short(&c.callee, 60), c.arguments.iter().map(|a| src.short(a, 80)).collect()),
        e => (src.short(e, 60), vec![]),
    }
}

impl<'a> Visit<'a> for P1<'_, '_> {
    fn visit_statement(&mut self, s: &Statement<'a>) {
        let saved = self.stmt_start;
        if !matches!(s, Statement::BlockStatement(_)) {
            self.stmt_start = s.span().start;
        }
        walk::walk_statement(self, s);
        self.stmt_start = saved;
    }

    fn visit_variable_declarator(&mut self, d: &VariableDeclarator<'a>) {
        if let (BindingPattern::BindingIdentifier(id), Some(init)) = (&d.id, &d.init) {
            let name = id.name.as_str().to_owned();
            let mut i = inner(init);
            // asyncHandler(async (req, res) => ...)
            if let Expression::CallExpression(c) = i
                && let Some(Expression::ArrowFunctionExpression(_) | Expression::FunctionExpression(_)) =
                    c.arguments.first().and_then(|a| a.as_expression()).map(inner)
            {
                i = inner(c.arguments[0].as_expression().unwrap_or(init));
            }
            match i {
                Expression::ArrowFunctionExpression(a) => {
                    let fp = FactoryParams {
                        first: a.params.items.first().and_then(|i| i.pattern.get_identifier_name()).map(|n| n.as_str().to_owned()),
                        rest: a.params.rest.as_ref().and_then(|r| r.rest.argument.get_identifier_name()).map(|n| n.as_str().to_owned()),
                    };
                    let returned: Vec<u32> = match &a.body {
                        ArrowFunctionBody::FunctionBody(b) => b
                            .statements
                            .iter()
                            .filter_map(|st| match st {
                                Statement::ReturnStatement(r) => r.argument.as_ref(),
                                _ => None,
                            })
                            .filter_map(fn_span_start)
                            .collect(),
                        body => body.as_expression().and_then(fn_span_start).into_iter().collect(),
                    };
                    for start in returned {
                        self.st.factory_params.insert(start, fp.clone());
                    }
                    // `const show = () => (req, res) => …` / `() => { return (req, res) => … }`
                    match &a.body {
                        ArrowFunctionBody::FunctionBody(b) => self.name_returned(&b.statements, &name),
                        body => {
                            if let Some(e) = body.as_expression() {
                                self.name_fn_expr(e, &name);
                            }
                        }
                    }
                    self.st.meta.insert(a.span.start, FnMeta { name, stmt_start: self.stmt_start, class: None, is_constructor: false });
                }
                Expression::FunctionExpression(f) => {
                    self.st.meta.insert(f.span.start, FnMeta { name, stmt_start: self.stmt_start, class: None, is_constructor: false });
                }
                Expression::ObjectExpression(o) if o.properties.len() >= 2 => self.object_decl(&name, o, d.span),
                Expression::TSAsExpression(_) | Expression::TSSatisfiesExpression(_) => {}
                _ => {}
            }
        }
        walk::walk_variable_declarator(self, d);
    }

    fn visit_function(&mut self, f: &Function<'a>, flags: ScopeFlags) {
        if let Some(id) = &f.id {
            self.st.meta.entry(f.span.start).or_insert(FnMeta {
                name: id.name.as_str().to_owned(),
                stmt_start: self.stmt_start,
                class: None,
                is_constructor: false,
            });
            // Handler factories: `function retrieveBasket() { return (req, res) => … }`.
            if let Some(body) = &f.body {
                self.name_returned(&body.statements, id.name.as_str());
            }
        }
        walk::walk_function(self, f, flags);
    }

    fn visit_class(&mut self, c: &Class<'a>) {
        let name = c.id.as_ref().map_or_else(|| "<class>".to_owned(), |i| i.name.as_str().to_owned());
        let mut prefix = String::new();
        let mut guards = Vec::new();
        for d in &c.decorators {
            let (n, args) = decorator_name(d, self.src);
            if n == "Controller"
                && let Expression::CallExpression(call) = &d.expression
                && let Some(p) = call.arguments.first().and_then(|a| a.as_expression()).and_then(lit_str)
            {
                prefix = p.to_owned();
            }
            if n == "UseGuards" {
                guards.extend(args.into_iter().map(|a| format!("UseGuards({a})")));
            }
        }
        self.st.class_stack.push((name, prefix, guards));
        walk::walk_class(self, c);
        self.st.class_stack.pop();
    }

    fn visit_method_definition(&mut self, m: &MethodDefinition<'a>) {
        let (class, prefix, class_guards) = self.st.class_stack.last().cloned().unwrap_or_default();
        let key = m.key.static_name().map_or_else(|| "<computed>".to_owned(), |k| k.into_owned());
        self.st.meta.insert(
            m.value.span.start,
            FnMeta {
                name: format!("{class}.{key}"),
                stmt_start: m.span.start,
                class: Some(class.clone()),
                is_constructor: m.kind == MethodDefinitionKind::Constructor,
            },
        );
        let mut route: Option<(String, String)> = None;
        let mut guards = class_guards;
        for d in &m.decorators {
            let (n, args) = decorator_name(d, self.src);
            if NEST_METHODS.contains(&n.as_str()) {
                let sub = if let Expression::CallExpression(c) = &d.expression {
                    c.arguments.first().and_then(|a| a.as_expression()).and_then(lit_str).unwrap_or("").to_owned()
                } else {
                    String::new()
                };
                let path = format!("/{}/{}", prefix.trim_matches('/'), sub.trim_matches('/')).replace("//", "/");
                let path = if path.len() > 1 { path.trim_end_matches('/').to_owned() } else { path };
                route = Some((n.to_ascii_uppercase(), path));
            }
            if n == "UseGuards" {
                guards.extend(args.into_iter().map(|a| format!("UseGuards({a})")));
            }
        }
        if let Some((method, path)) = route {
            self.st.handlers.push(HandlerReg {
                method,
                path,
                middleware: guards,
                location: self.src.loc(m.span),
                target: HandlerTarget::Span(m.value.span.start),
                args: vec![],
            });
        }
        walk::walk_method_definition(self, m);
    }

    fn visit_object_property(&mut self, p: &ObjectProperty<'a>) {
        // GraphQL resolver maps: `{ Query: { note: (parent, args, context) => … }, Mutation: { … } }`.
        // Each resolver is an entry point: `args` is client input, `context.user` the principal.
        if let Some(k) = p.key.static_name()
            && matches!(k.as_ref(), "Query" | "Mutation" | "Subscription")
            && let Expression::ObjectExpression(o) = inner(&p.value)
            && GRAPHQL_FILE.is_match(self.src.text)
        {
            for rp in &o.properties {
                let ObjectPropertyKind::ObjectProperty(rp) = rp else { continue };
                let (Some(field), Some((start, n))) = (
                    rp.key.static_name(),
                    match inner(&rp.value) {
                        Expression::ArrowFunctionExpression(a) => Some((a.span.start, a.params.items.len())),
                        Expression::FunctionExpression(f) => Some((f.span.start, f.params.items.len())),
                        _ => None,
                    },
                ) else {
                    continue;
                };
                if n >= 2 {
                    self.st.handlers.push(HandlerReg {
                        method: k.to_ascii_uppercase(),
                        path: format!("/graphql/{field}"),
                        middleware: vec![],
                        location: self.src.loc(rp.span),
                        target: HandlerTarget::Span(start),
                        args: vec![],
                    });
                }
            }
        }
        if let Some(k) = p.key.static_name() {
            match inner(&p.value) {
                Expression::ArrowFunctionExpression(a) => {
                    self.st.meta.entry(a.span.start).or_insert(FnMeta { name: k.into_owned(), stmt_start: p.span.start, class: None, is_constructor: false });
                }
                Expression::FunctionExpression(f) => {
                    self.st.meta.entry(f.span.start).or_insert(FnMeta { name: k.into_owned(), stmt_start: p.span.start, class: None, is_constructor: false });
                }
                _ => {}
            }
        }
        walk::walk_object_property(self, p);
    }

    fn visit_export_declaration(&mut self, e: &ExportDeclaration<'a>) {
        match &e.declaration {
            Declaration::FunctionDeclaration(f) => {
                if let Some(id) = &f.id {
                    self.st.exported.insert(id.name.as_str().to_owned());
                }
            }
            Declaration::VariableDeclaration(v) => {
                for d in &v.declarations {
                    for n in crate::expr::binding_names(&d.id) {
                        self.st.exported.insert(n);
                    }
                }
            }
            Declaration::ClassDeclaration(c) => {
                if let Some(id) = &c.id {
                    self.st.exported_classes.insert(id.name.as_str().to_owned());
                }
            }
            _ => {}
        }
        walk::walk_export_declaration(self, e);
    }

    fn visit_export_named_declaration(&mut self, e: &ExportNamedDeclaration<'a>) {
        for s in &e.specifiers {
            self.st.exported.insert(s.local.name().to_string());
        }
        walk::walk_export_named_declaration(self, e);
    }

    fn visit_export_from_declaration(&mut self, e: &ExportFromDeclaration<'a>) {
        self.st.imports.insert(e.source.value.as_str().to_owned());
        walk::walk_export_from_declaration(self, e);
    }

    fn visit_export_default_declaration(&mut self, e: &ExportDefaultDeclaration<'a>) {
        match &e.declaration {
            ExportDefaultDeclarationKind::FunctionDeclaration(f) => {
                let name = f.id.as_ref().map_or_else(|| "default".to_owned(), |i| i.name.as_str().to_owned());
                self.st.meta.entry(f.span.start).or_insert(FnMeta { name: name.clone(), stmt_start: e.span.start, class: None, is_constructor: false });
                self.st.exported.insert(name);
            }
            ExportDefaultDeclarationKind::ClassDeclaration(c) => {
                if let Some(id) = &c.id {
                    self.st.exported_classes.insert(id.name.as_str().to_owned());
                }
            }
            ExportDefaultDeclarationKind::Identifier(id) => {
                self.st.exported.insert(id.name.as_str().to_owned());
            }
            _ => {}
        }
        walk::walk_export_default_declaration(self, e);
    }

    fn visit_export_all_declaration(&mut self, e: &ExportAllDeclaration<'a>) {
        self.st.imports.insert(e.source.value.as_str().to_owned());
    }

    fn visit_import_declaration(&mut self, i: &ImportDeclaration<'a>) {
        let spec = i.source.value.as_str().to_owned();
        self.st.imports.insert(spec.clone());
        for s in i.specifiers.iter().flatten() {
            self.st.import_bindings.insert(s.local().name.as_str().to_owned(), spec.clone());
        }
    }

    fn visit_assignment_expression(&mut self, a: &AssignmentExpression<'a>) {
        // module.exports = { a, b } / module.exports.x = / exports.x =
        let lhs = self.src.slice(a.left.span());
        if lhs == "module.exports" {
            if let Expression::ObjectExpression(o) = inner(&a.right) {
                for p in &o.properties {
                    if let ObjectPropertyKind::ObjectProperty(op) = p {
                        if let Some(k) = op.key.static_name() {
                            self.st.exported.insert(k.into_owned());
                        }
                        if let Expression::Identifier(id) = inner(&op.value) {
                            self.st.exported.insert(id.name.as_str().to_owned());
                        }
                    }
                }
            } else if let Expression::Identifier(id) = inner(&a.right) {
                self.st.exported.insert(id.name.as_str().to_owned());
            }
        } else if let Some(name) = lhs
            .strip_prefix("this.")
            .or_else(|| lhs.split_once(".prototype.").map(|(_, n)| n))
            .filter(|n| n.chars().all(|c| c.is_alphanumeric() || c == '_' || c == '$'))
        {
            // Constructor-style handlers: `this.show = (req, res) => …`, `Foo.prototype.show = function…`
            match inner(&a.right) {
                Expression::ArrowFunctionExpression(f) => {
                    self.st.meta.entry(f.span.start).or_insert(FnMeta {
                        name: name.to_owned(),
                        stmt_start: self.stmt_start,
                        class: None,
                        is_constructor: false,
                    });
                }
                Expression::FunctionExpression(f) => {
                    self.st.meta.entry(f.span.start).or_insert(FnMeta {
                        name: name.to_owned(),
                        stmt_start: self.stmt_start,
                        class: None,
                        is_constructor: false,
                    });
                }
                _ => {}
            }
        } else if let Some(name) = lhs.strip_prefix("module.exports.").or_else(|| lhs.strip_prefix("exports.")) {
            self.st.exported.insert(name.to_owned());
            if let Expression::ArrowFunctionExpression(f) = inner(&a.right) {
                self.st.meta.entry(f.span.start).or_insert(FnMeta { name: name.to_owned(), stmt_start: self.stmt_start, class: None, is_constructor: false });
            }
            if let Expression::FunctionExpression(f) = inner(&a.right) {
                self.st.meta.entry(f.span.start).or_insert(FnMeta { name: name.to_owned(), stmt_start: self.stmt_start, class: None, is_constructor: false });
            }
        }
        walk::walk_assignment_expression(self, a);
    }

    fn visit_call_expression(&mut self, c: &CallExpression<'a>) {
        // app.use("/prefix", mw..., router) / router.use(mw)
        if let Some(m) = c.callee.get_inner_expression().as_member_expression()
            && m.static_property_name() == Some("use")
            && !c.arguments.is_empty()
        {
            let args: Vec<&Expression<'_>> = c.arguments.iter().filter_map(|a| a.as_expression()).collect();
            let (prefix, rest) = match args.first().and_then(|a| lit_str(a)) {
                Some(p) if p.starts_with('/') => (p.to_owned(), &args[1..]),
                _ => (String::new(), &args[..]),
            };
            if let Some((last, mws)) = rest.split_last() {
                let target = match inner(last) {
                    Expression::Identifier(id) if self.st.import_bindings.contains_key(id.name.as_str()) => Some(id.name.as_str().to_owned()),
                    _ => None,
                };
                let mws_all: Vec<String> = if target.is_some() {
                    mws.iter().map(|a| collapse(self.src.slice(a.span()), 80)).collect()
                } else {
                    rest.iter().map(|a| collapse(self.src.slice(a.span()), 80)).collect()
                };
                let target = target.map(|t| (t, collapse(self.src.slice(last.span()), 80)));
                self.st.mounts.push((prefix, mws_all, target, self.src.loc(c.span)));
            }
        }
        if c.is_require_call()
            && let Some(s) = c.arguments.first().and_then(|a| a.as_expression()).and_then(lit_str)
        {
            self.st.imports.insert(s.to_owned());
        }
        // router.get("/x/:id", mw, handler)  or  router.route("/x/:id").get(mw, handler, after)
        if let Some(member) = c.callee.get_inner_expression().as_member_expression()
            && let Some(m) = member.static_property_name()
        {
            let m = m.to_ascii_lowercase();
            let args: Vec<&Expression<'_>> = c.arguments.iter().filter_map(|x| x.as_expression()).collect();
            let direct = args.first().and_then(|a| lit_str(a)).filter(|p| p.starts_with('/')).map(|p| (p.to_owned(), 1usize));
            let chained = route_chain_path(member.object()).map(|p| (p, 0usize));
            if HTTP_METHODS.contains(&m.as_str())
                && let Some((path, skip)) = direct.or(chained)
                && args.len() > skip
            {
                let rest = &args[skip..];
                let route_args: Vec<RouteArg> = rest
                    .iter()
                    .map(|a| RouteArg {
                        text: collapse(self.src.slice(a.span()), 80),
                        name: match handler_target(a) {
                            Some(HandlerTarget::Name(n)) => Some(n),
                            _ => None,
                        },
                    })
                    .collect();
                // Inline function handler: the last function-valued argument; otherwise resolved by name later.
                let inline = rest.iter().rposition(|a| matches!(inner(a), Expression::ArrowFunctionExpression(_) | Expression::FunctionExpression(_)) || matches!(inner(a), Expression::CallExpression(w) if w.arguments.first().and_then(|x| x.as_expression()).is_some_and(|x| matches!(inner(x), Expression::ArrowFunctionExpression(_) | Expression::FunctionExpression(_)))));
                let (target, middleware) = match inline {
                    Some(i) => (rest.get(i).and_then(|a| handler_target(a)), route_args[..i].iter().map(|r| r.text.clone()).collect::<Vec<_>>()),
                    // Named handler: the last argument that resolves (a trailing `guard.check([...])`
                    // does not); the model re-resolves against `args` to find the real body.
                    None => match rest.iter().rposition(|a| handler_target(a).is_some()) {
                        Some(i) => (handler_target(rest[i]), route_args[..i].iter().map(|r| r.text.clone()).collect()),
                        None => (None, vec![]),
                    },
                };
                let handler_name = match &target {
                    Some(HandlerTarget::Name(n)) => n.clone(),
                    _ => format!("<route {} {path}>", m.to_ascii_uppercase()),
                };
                let location = self.src.loc(c.span);
                self.st.routes.push(RouteFact {
                    method: m.to_ascii_uppercase(),
                    path: path.clone(),
                    handler: handler_name.clone(),
                    location: location.clone(),
                });
                if let Some(target) = target {
                    if let HandlerTarget::Span(s) = &target {
                        self.st.meta.entry(*s).or_insert(FnMeta { name: handler_name, stmt_start: c.span.start, class: None, is_constructor: false });
                    }
                    self.st.handlers.push(HandlerReg {
                        method: m.to_ascii_uppercase(),
                        path,
                        middleware,
                        location,
                        target,
                        args: if inline.is_some() { vec![] } else { route_args },
                    });
                }
            }
        }
        if let Expression::ImportExpression(_) = &c.callee {}
        walk::walk_call_expression(self, c);
    }

    fn visit_import_expression(&mut self, i: &ImportExpression<'a>) {
        if let Some(s) = lit_str(&i.source) {
            self.st.imports.insert(s.to_owned());
        }
        walk::walk_import_expression(self, i);
    }

    fn visit_ts_enum_declaration(&mut self, e: &TSEnumDeclaration<'a>) {
        let members = e
            .body
            .members
            .iter()
            .map(|m| match (&m.initializer, &m.id) {
                (Some(Expression::StringLiteral(s)), _) => s.value.as_str().to_owned(),
                (_, TSEnumMemberName::Identifier(i)) => i.name.as_str().to_owned(),
                (_, TSEnumMemberName::String(s) | TSEnumMemberName::ComputedString(s)) => s.value.as_str().to_owned(),
                (_, TSEnumMemberName::ComputedTemplateString(t)) => self.src.slice(t.span).to_owned(),
            })
            .collect();
        self.st.enums.push(EnumFact { name: e.id.name.as_str().to_owned(), members, location: self.src.loc(e.span), kind: EnumKind::Enum });
        walk::walk_ts_enum_declaration(self, e);
    }

    fn visit_ts_type_alias_declaration(&mut self, t: &TSTypeAliasDeclaration<'a>) {
        if let TSType::TSUnionType(u) = &t.type_annotation {
            let lits: Option<Vec<String>> = u
                .types
                .iter()
                .map(|ty| match ty {
                    TSType::TSLiteralType(l) => match &l.literal {
                        TSLiteral::StringLiteral(s) => Some(s.value.as_str().to_owned()),
                        _ => None,
                    },
                    _ => None,
                })
                .collect();
            if let Some(members) = lits.filter(|m| m.len() >= 2) {
                self.st.enums.push(EnumFact { name: t.id.name.as_str().to_owned(), members, location: self.src.loc(t.span), kind: EnumKind::Union });
            }
        }
        walk::walk_ts_type_alias_declaration(self, t);
    }
}

impl P1<'_, '_> {
    fn name_fn_expr(&mut self, e: &Expression<'_>, name: &str) {
        match inner(e) {
            Expression::ArrowFunctionExpression(f) => {
                self.st.meta.entry(f.span.start).or_insert(FnMeta { name: name.to_owned(), stmt_start: f.span.start, class: None, is_constructor: false });
            }
            Expression::FunctionExpression(f) => {
                self.st.meta.entry(f.span.start).or_insert(FnMeta { name: name.to_owned(), stmt_start: f.span.start, class: None, is_constructor: false });
            }
            _ => {}
        }
    }

    fn name_returned(&mut self, stmts: &[Statement<'_>], name: &str) {
        for st in stmts {
            if let Statement::ReturnStatement(r) = st
                && let Some(arg) = &r.argument
            {
                self.name_fn_expr(arg, name);
            }
        }
    }

    /// `const Status = { A: "A", B: "B" } as const` (enum) or `const ALLOWED = { A: ["B"] }` (transition table).
    fn object_decl(&mut self, name: &str, o: &ObjectExpression<'_>, span: Span) {
        let mut values = Vec::new();
        let mut edges = Vec::new();
        let mut is_enum = name.starts_with(char::is_uppercase);
        let mut is_table = true;
        for p in &o.properties {
            let ObjectPropertyKind::ObjectProperty(op) = p else {
                return;
            };
            let key = if op.computed { op.key.as_expression().and_then(literal_member) } else { op.key.static_name().map(|k| k.into_owned()) };
            let Some(key) = key else { return };
            match inner(&op.value) {
                Expression::StringLiteral(s) => {
                    values.push(s.value.as_str().to_owned());
                    is_table = false;
                }
                Expression::ArrayExpression(arr) => {
                    is_enum = false;
                    let targets: Option<Vec<String>> = arr.elements.iter().map(|el| el.as_expression().and_then(literal_member)).collect();
                    match targets {
                        Some(ts) => edges.extend(ts.into_iter().map(|t| (key.clone(), t))),
                        None => is_table = false,
                    }
                }
                _ => {
                    is_enum = false;
                    is_table = false;
                }
            }
        }
        if is_enum && values.len() >= 2 && values.len() == o.properties.len() {
            self.st.enums.push(EnumFact { name: name.to_owned(), members: values, location: self.src.loc(span), kind: EnumKind::ConstObject });
        } else if is_table && !o.properties.is_empty() {
            self.st.tables.push(TransitionTableFact { name: name.to_owned(), edges, location: self.src.loc(span) });
        }
    }
}

fn annotations(comments: &[Comment], src: &Source<'_>, stmt_start: u32) -> Vec<String> {
    static TAG: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"@proof-?it\s+([A-Z][A-Z0-9]*-\d{3}(?:[\s,]+[A-Z][A-Z0-9]*-\d{3})*)").expect("static regex"));
    static ID: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"[A-Z][A-Z0-9]*-\d{3}").expect("static regex"));
    let mut out = Vec::new();
    for c in comments.iter().filter(|c| c.span.end <= stmt_start) {
        let gap = src.slice(Span::new(c.span.end, stmt_start));
        if !gap.trim().is_empty() && !gap.trim().starts_with('*') {
            continue;
        }
        if gap.len() > 200 {
            continue;
        }
        let text = src.slice(c.span);
        if let Some(m) = TAG.captures(text) {
            out.extend(ID.find_iter(m.get(1).map_or("", |x| x.as_str())).map(|x| x.as_str().to_owned()));
        }
    }
    out.sort();
    out.dedup();
    out
}

/// `req.body.UserId = <non-request value>` in middleware: the field becomes server-controlled.
/// For middleware-shaped functions (`(req, res, next)`), what the body can do.
/// Read from the AST, so comments and strings cannot fake a check.
fn guard_fact(f: &FnRef<'_, '_>, params: &[String], src: &Source<'_>) -> Option<GuardFact> {
    let next = params.get(2).filter(|n| matches!(n.as_str(), "next" | "done" | "cb" | "callback" | "_next"))?.clone();
    if !matches!(params.get(1).map(String::as_str), Some("res" | "response" | "reply" | "_res" | "resp")) {
        return None;
    }
    struct G<'c, 's> {
        src: &'c Source<'s>,
        next: String,
        g: GuardFact,
    }
    impl<'a> Visit<'a> for G<'_, '_> {
        fn visit_call_expression(&mut self, c: &CallExpression<'a>) {
            let callee = self.src.slice(c.callee.span()).split_whitespace().collect::<String>();
            let first = c.arguments.first().and_then(|a| a.as_expression()).map(inner);
            let status = |e: Option<&Expression<'_>>| matches!(e, Some(Expression::NumericLiteral(n)) if n.value >= 400.0);
            if (re!(r"^(res|response|reply|resp)\.(status|sendStatus|code)$").is_match(&callee) && status(first))
                || re!(r"^(res|response|reply|resp)\.redirect$").is_match(&callee)
                || (callee == self.next && !c.arguments.is_empty())
            {
                self.g.can_deny = true;
            }
            if re!(r"(?i)verify|jwt|passport|authenticat|decode|getSession|validateToken|checkToken").is_match(&callee) {
                self.g.checks_identity = true;
            }
            walk::walk_call_expression(self, c);
        }
        fn visit_throw_statement(&mut self, t: &ThrowStatement<'a>) {
            self.g.can_deny = true;
            walk::walk_throw_statement(self, t);
        }
        fn visit_static_member_expression(&mut self, m: &StaticMemberExpression<'a>) {
            let p = m.property.name.as_str();
            if re!(r"(?i)^(role|roles|isadmin|admin|permissions?|scopes?|issuperadmin|usertype|accounttype|issuperuser|isstaff)$").is_match(p) {
                self.g.checks_role = true;
            }
            if re!(r"(?i)^(user|session|authorization|token)$").is_match(p) {
                self.g.checks_identity = true;
            }
            walk::walk_static_member_expression(self, m);
        }
        fn visit_identifier_reference(&mut self, i: &IdentifierReference<'a>) {
            if re!(r"(?i)^(roles?|allowedroles|requiredroles|permissions?)$").is_match(i.name.as_str()) {
                self.g.checks_role = true;
            }
        }
        fn visit_string_literal(&mut self, s: &StringLiteral<'a>) {
            if re!(r"(?i)^(admin|super_?admin|superuser|staff|authorization)$").is_match(s.value.as_str()) {
                self.g.checks_role |= !s.value.eq_ignore_ascii_case("authorization");
                self.g.names_admin |= !s.value.eq_ignore_ascii_case("authorization");
                self.g.checks_identity |= s.value.eq_ignore_ascii_case("authorization");
            }
        }
    }
    let mut v = G { src, next, g: GuardFact::default() };
    match (f.statements(), f.expression_body()) {
        (Some(stmts), _) => {
            for s in stmts {
                v.visit_statement(s);
            }
        }
        (None, Some(e)) => v.visit_expression(e),
        _ => {}
    }
    Some(v.g)
}

/// Span start of a function expression (arrow or `function`), if `e` is one.
fn fn_span_start(e: &Expression<'_>) -> Option<u32> {
    match inner(e) {
        Expression::ArrowFunctionExpression(f) => Some(f.span.start),
        Expression::FunctionExpression(f) => Some(f.span.start),
        _ => None,
    }
}

/// `const NAME = ['a', 'b'] [as const]` at module level: name → strings.
/// Only top-level `const`s, so a binding cannot be shadowed or reassigned.
fn top_level_string_arrays(body: &[Statement<'_>]) -> HashMap<String, Vec<String>> {
    let mut out = HashMap::new();
    for s in body {
        let decl = match s {
            Statement::VariableDeclaration(d) => d,
            // `export const NAME = [...]`
            Statement::ExportDeclaration(e) => match &e.declaration {
                Declaration::VariableDeclaration(d) => d,
                _ => continue,
            },
            _ => continue,
        };
        if decl.kind != VariableDeclarationKind::Const {
            continue;
        }
        for d in &decl.declarations {
            if let (BindingPattern::BindingIdentifier(id), Some(init)) = (&d.id, &d.init)
                && let Some(v) = string_array(init, &HashMap::new())
            {
                out.insert(id.name.as_str().to_owned(), v);
            }
        }
    }
    out
}

/// An array of string literals, written inline or as a top-level constant.
fn string_array(e: &Expression<'_>, consts: &HashMap<String, Vec<String>>) -> Option<Vec<String>> {
    match inner(e) {
        Expression::ArrayExpression(a) => {
            a.elements.iter().map(|el| el.as_expression().and_then(|x| lit_str(x)).map(str::to_owned)).collect::<Option<Vec<_>>>().filter(|v| !v.is_empty())
        }
        Expression::Identifier(id) => consts.get(id.name.as_str()).cloned(),
        _ => None,
    }
}

/// The exact set of roles a middleware lets through, or `None` when it cannot
/// be read with certainty. Recognised, as top-level statements that run before
/// anything calls `next`:
///
///   if (!ROLES.includes(req.….role)) <deny>      → ROLES
///   if (req.….role !== 'a' [&& … !== 'b']) <deny> → {a, b}
///
/// `<deny>` must end in `return` or `throw`, must not call `next()` without an
/// error, and must contain a denial (status >= 400, throw, `next(err)`). Several
/// such checks intersect. Anything else (a check inside a branch, after `next`,
/// a role read through a variable, `===` that denies admins) yields `None`, so the
/// guard cannot support a proof.
///
/// In a function returned by a factory, `!roles.includes(…)` where `roles` is the
/// factory's rest parameter yields `["$args"]` (all call-site arguments) and its
/// first parameter yields `["$arg0"]`; the model reads the literals at the call.
fn admitted_roles(
    f: &FnRef<'_, '_>,
    params: &[String],
    src: &Source<'_>,
    consts: &HashMap<String, Vec<String>>,
    factory: Option<&FactoryParams>,
) -> Option<Vec<String>> {
    let req = params.first()?.as_str();
    let next = params.get(2)?.as_str();
    let stmts = f.statements()?;
    let is_role = |e: &Expression<'_>| {
        let t = src.slice(inner(e).span()).split_whitespace().collect::<String>();
        t.starts_with(&format!("{req}.")) && t.ends_with(".role")
    };
    // Roles admitted by an `if` test that denies when it holds, if recognised.
    fn admitted<'a>(
        test: &Expression<'a>,
        is_role: &dyn Fn(&Expression<'a>) -> bool,
        consts: &HashMap<String, Vec<String>>,
        factory: Option<&FactoryParams>,
    ) -> Option<Vec<String>> {
        match inner(test) {
            // !ROLES.includes(role)
            Expression::UnaryExpression(u) if u.operator == UnaryOperator::LogicalNot => {
                let Expression::CallExpression(c) = inner(&u.argument) else { return None };
                let m = c.callee.get_inner_expression().as_member_expression()?;
                if m.static_property_name() != Some("includes") || c.arguments.len() != 1 {
                    return None;
                }
                let arg = c.arguments[0].as_expression()?;
                if !is_role(arg) {
                    return None;
                }
                if let Some(v) = string_array(m.object(), consts) {
                    return Some(v);
                }
                let Expression::Identifier(id) = inner(m.object()) else { return None };
                let fp = factory?;
                if fp.rest.as_deref() == Some(id.name.as_str()) {
                    Some(vec!["$args".to_owned()])
                } else if fp.first.as_deref() == Some(id.name.as_str()) {
                    Some(vec!["$arg0".to_owned()])
                } else {
                    None
                }
            }
            // role !== 'a'
            Expression::BinaryExpression(b) if b.operator == BinaryOperator::StrictInequality || b.operator == BinaryOperator::Inequality => {
                let (role, lit) = if is_role(&b.left) { (&b.left, &b.right) } else { (&b.right, &b.left) };
                if !is_role(role) {
                    return None;
                }
                lit_str(inner(lit)).map(|s| vec![s.to_owned()])
            }
            // role !== 'a' && role !== 'b'  (denies unless role is a or b)
            Expression::LogicalExpression(l) if l.operator == LogicalOperator::And => {
                let (a, b) = (admitted(&l.left, is_role, consts, factory)?, admitted(&l.right, is_role, consts, factory)?);
                if a.iter().chain(&b).any(|r| r.starts_with('$')) {
                    return None;
                }
                Some(a.into_iter().chain(b).collect())
            }
            // A || B  (denies if either holds): passing needs every recognised
            // disjunct false, so the roles are within each recognised set.
            Expression::LogicalExpression(l) if l.operator == LogicalOperator::Or => {
                match (admitted(&l.left, is_role, consts, factory), admitted(&l.right, is_role, consts, factory)) {
                    (Some(a), Some(b)) => intersect(a, b),
                    (Some(a), None) | (None, Some(a)) => Some(a),
                    (None, None) => None,
                }
            }
            _ => None,
        }
    }
    /// Roles in both sets; call-site placeholders (`$args`) only combine with
    /// themselves, otherwise the result is unknown.
    fn intersect(a: Vec<String>, b: Vec<String>) -> Option<Vec<String>> {
        if a.iter().chain(&b).any(|r| r.starts_with('$')) {
            return (a == b).then_some(a);
        }
        Some(a.into_iter().filter(|r| b.contains(r)).collect())
    }
    struct Exit<'n> {
        next: &'n str,
        /// `next()` without an error: lets the request through.
        passes: bool,
        /// Any call to `next`, with or without an error.
        calls_next: bool,
        denies: bool,
    }
    impl<'a> Visit<'a> for Exit<'_> {
        fn visit_call_expression(&mut self, c: &CallExpression<'a>) {
            if let Expression::Identifier(id) = c.callee.get_inner_expression()
                && id.name.as_str() == self.next
            {
                self.calls_next = true;
                if c.arguments.is_empty() { self.passes = true } else { self.denies = true }
            }
            if let Some(m) = c.callee.get_inner_expression().as_member_expression()
                && matches!(m.static_property_name(), Some("status" | "sendStatus" | "code"))
                && c.arguments.first().and_then(|a| a.as_expression()).is_some_and(|a| matches!(inner(a), Expression::NumericLiteral(n) if n.value >= 400.0))
            {
                self.denies = true;
            }
            walk::walk_call_expression(self, c);
        }
        fn visit_throw_statement(&mut self, t: &ThrowStatement<'a>) {
            self.denies = true;
            walk::walk_throw_statement(self, t);
        }
    }
    let exits_denying = |s: &Statement<'_>| {
        let last = match s {
            Statement::BlockStatement(b) => b.body.last(),
            other => Some(other),
        };
        if !matches!(last, Some(Statement::ReturnStatement(_) | Statement::ThrowStatement(_))) {
            return false;
        }
        let mut e = Exit { next, passes: false, calls_next: false, denies: false };
        e.visit_statement(s);
        e.denies && !e.passes
    };
    let calls_next = |s: &Statement<'_>| {
        let mut e = Exit { next, passes: false, calls_next: false, denies: false };
        e.visit_statement(s);
        e.calls_next
    };
    let mut result: Option<Vec<String>> = None;
    for s in stmts {
        if let Statement::IfStatement(i) = s
            && i.alternate.is_none()
            && exits_denying(&i.consequent)
            && let Some(roles) = admitted(&i.test, &is_role, consts, factory)
        {
            result = match result {
                None => Some(roles),
                Some(prev) => Some(intersect(prev, roles)?),
            };
            continue;
        }
        if calls_next(s) {
            break;
        }
    }
    result.map(|mut v| {
        v.sort();
        v.dedup();
        v
    })
}

fn request_overrides(stmts: &[Statement<'_>], req: &str, src: &Source<'_>) -> Vec<String> {
    struct O<'q, 'c, 's> {
        req: &'q str,
        src: &'c Source<'s>,
        out: Vec<String>,
    }
    impl<'a> Visit<'a> for O<'_, '_, '_> {
        fn visit_assignment_expression(&mut self, a: &AssignmentExpression<'a>) {
            let aliases = crate::expr::Aliases::default();
            let conv = Conv::new(self.src, &aliases);
            if let Some(m) = a.left.as_member_expression() {
                let lhs = m.object();
                if let (Some(obj), Some(field)) = (conv.raw_path(lhs), m.static_property_name()) {
                    let from_request = conv
                        .paths_in(&a.right)
                        .iter()
                        .any(|p| ["body", "query", "params", "headers", "cookies"].iter().any(|k| p.starts_with(&format!("{}.{k}", self.req))));
                    for k in ["body", "query", "params"] {
                        if obj == format!("{}.{k}", self.req) && !from_request {
                            self.out.push(format!("req.{k}.{field}"));
                        }
                    }
                }
            }
            walk::walk_assignment_expression(self, a);
        }
    }
    let mut o = O { req, src, out: vec![] };
    for st in stmts {
        o.visit_statement(st);
    }
    o.out.sort();
    o.out.dedup();
    o.out
}

/// Direct writes to a balance field (not inside nested functions).
fn balance_writes(stmts: &[Statement<'_>]) -> bool {
    struct B(bool);
    impl<'a> Visit<'a> for B {
        fn visit_assignment_expression(&mut self, a: &AssignmentExpression<'a>) {
            if a.left.as_member_expression().and_then(|m| m.static_property_name()).is_some_and(|n| BALANCE.is_match(n)) {
                self.0 = true;
            }
            walk::walk_assignment_expression(self, a);
        }
        fn visit_update_expression(&mut self, u: &UpdateExpression<'a>) {
            if u.argument.as_member_expression().and_then(|m| m.static_property_name()).is_some_and(|n| BALANCE.is_match(n)) {
                self.0 = true;
            }
        }
        fn visit_function(&mut self, _: &Function<'a>, _: ScopeFlags) {}
        fn visit_arrow_function_expression(&mut self, _: &ArrowFunctionExpression<'a>) {}
    }
    let mut b = B(false);
    for s in stmts {
        b.visit_statement(s);
    }
    b.0
}

fn stmt_writes_balance(s: &Statement<'_>) -> bool {
    balance_writes(std::slice::from_ref(s))
}

/// Top-level statement sequence of a ledger function, classified.
fn ledger_stmts(stmts: &[Statement<'_>], src: &Source<'_>, aliases: &Aliases) -> Vec<LedgerStmt> {
    let conv = Conv::new(src, aliases);
    let mut out = Vec::new();
    for s in stmts {
        let location = src.loc(s.span());
        match s {
            Statement::VariableDeclaration(v) => {
                for d in &v.declarations {
                    if let (BindingPattern::BindingIdentifier(id), Some(init)) = (&d.id, &d.init) {
                        out.push(LedgerStmt::Let { name: id.name.as_str().to_owned(), value: conv.val(init), location: src.loc(d.span) });
                    }
                }
            }
            Statement::IfStatement(i) if i.alternate.is_none() && exits(&i.consequent, src, false) => {
                out.push(LedgerStmt::ExitGuard { cond: conv.cond(&i.test), text: src.short(&i.test, 120), location });
            }
            Statement::ExpressionStatement(e) => {
                let ex = inner(&e.expression);
                match ex {
                    Expression::AssignmentExpression(a)
                        if a.left.as_member_expression().and_then(|m| m.static_property_name()).is_some_and(|n| BALANCE.is_match(n)) =>
                    {
                        let Some(m) = a.left.as_member_expression() else {
                            continue;
                        };
                        let recv = conv.raw_path(m.object()).unwrap_or_else(|| src.short(m.object(), 60));
                        let field = m.static_property_name().map(|f| f.to_string()).unwrap_or_default();
                        let op = match a.operator {
                            AssignmentOperator::Assign => Some(AssignOp::Set),
                            AssignmentOperator::Addition => Some(AssignOp::Add),
                            AssignmentOperator::Subtraction => Some(AssignOp::Sub),
                            _ => None,
                        };
                        match op {
                            Some(op) => out.push(LedgerStmt::BalanceWrite {
                                receiver: recv,
                                field,
                                op,
                                value: conv.val(&a.right),
                                text: src.short(&**a, 120),
                                location,
                            }),
                            None => out.push(LedgerStmt::Unsupported { reason: format!("operator `{}` on a balance", a.operator.as_str()), location }),
                        }
                    }
                    Expression::UpdateExpression(u) if u.argument.as_member_expression().is_some() && stmt_writes_balance(s) => {
                        let what = if u.operator == UpdateOperator::Increment { "++" } else { "--" };
                        out.push(LedgerStmt::Unsupported { reason: format!("`{what}` on a balance"), location });
                    }
                    _ if stmt_writes_balance(s) => {
                        out.push(LedgerStmt::Unsupported { reason: format!("unsupported balance update `{}`", src.short(&e.expression, 60)), location })
                    }
                    _ => {}
                }
            }
            Statement::ReturnStatement(_) => {
                out.push(LedgerStmt::Return { location });
                break;
            }
            Statement::IfStatement(_) if stmt_writes_balance(s) => {
                out.push(LedgerStmt::Unsupported { reason: "balance updated inside a conditional branch (path merging is not modeled)".into(), location })
            }
            _ if stmt_writes_balance(s) => {
                out.push(LedgerStmt::Unsupported { reason: "balance updated inside a loop/try/nested block (not modeled)".into(), location })
            }
            _ => {}
        }
    }
    out
}

pub struct ModuleOut {
    pub facts: ModuleFacts,
}

struct P2<'c, 's> {
    string_arrays: &'c HashMap<String, Vec<String>>,
    src: &'c Source<'s>,
    p1: &'c Pass1,
    comments: &'c [Comment],
    functions: Vec<FunctionFact>,
    state_writes: Vec<StateWriteFact>,
    handlers: Vec<HandlerFact>,
    handler_bodies: Vec<HandlerFact>,
    matched: std::collections::HashSet<usize>,
    ledger: Vec<LedgerFunctionFact>,
}

impl P2<'_, '_> {
    fn process(&mut self, f: FnRef<'_, '_>) {
        let span = f.span();
        let meta = self.p1.meta.get(&span.start).cloned().unwrap_or_else(|| {
            let (line, _) = self.src.line_col(span.start);
            FnMeta { name: format!("<anonymous@{line}>"), stmt_start: span.start, class: None, is_constructor: false }
        });
        let params = param_names(f.params());
        let ptypes = param_types(f.params(), self.src);
        let simple = meta.name.rsplit('.').next().unwrap_or(&meta.name).to_owned();
        let exported = self.p1.exported.contains(&meta.name) || meta.class.as_ref().is_some_and(|c| self.p1.exported_classes.contains(c));
        let statements = f.statements().map_or(1, <[Statement<'_>]>::len);
        let annotations = annotations(self.comments, self.src, meta.stmt_start);
        let request_overrides = f.statements().map(|st| request_overrides(st, params.first().map_or("req", String::as_str), self.src)).unwrap_or_default();
        let guard = guard_fact(&f, &params, self.src);
        let factory = self.p1.factory_params.get(&span.start);
        let admits_roles = guard.and_then(|_| admitted_roles(&f, &params, self.src, self.string_arrays, factory));
        self.functions.push(FunctionFact {
            name: meta.name.clone(),
            params: params.clone(),
            location: self.src.loc(span),
            exported,
            is_async: f.is_async(),
            statements,
            annotations: annotations.clone(),
            request_overrides,
            guard,
            admits_roles,
        });

        let stmts = f.statements();
        let aliases = stmts.map(|s| collect_aliases(self.src, s)).unwrap_or_default();
        let info = || FnInfo { name: &meta.name, params: &params, param_types: &ptypes, exported, is_constructor: meta.is_constructor };

        let mut w = Walker::new(self.src, &aliases, info(), false);
        match (stmts, f.expression_body()) {
            (Some(s), _) => w.walk_body(s),
            (None, Some(e)) => w.walk_expression_body(e),
            _ => {}
        }
        self.state_writes.extend(w.out.state_writes);

        // HTTP handler?
        let regs: Vec<&HandlerReg> = self
            .p1
            .handlers
            .iter()
            .filter(|r| match &r.target {
                HandlerTarget::Span(s) => *s == span.start,
                HandlerTarget::Name(n) => *n == meta.name || *n == simple,
            })
            .collect();
        for (i, r) in self.p1.handlers.iter().enumerate() {
            if match &r.target {
                HandlerTarget::Span(s) => *s == span.start,
                HandlerTarget::Name(n) => *n == meta.name || *n == simple,
            } {
                self.matched.insert(i);
            }
        }
        let annotated_handler = annotations.iter().any(|a| a.starts_with("AUTHZ"));
        // `(req, res, …)`-shaped functions may be registered as handlers in other files.
        let handler_shaped =
            params.len() >= 2 && matches!(params[0].as_str(), "req" | "request" | "ctx") && matches!(params[1].as_str(), "res" | "response" | "reply" | "h");
        if !regs.is_empty() || annotated_handler || handler_shaped {
            let mut hw = Walker::new(self.src, &aliases, info(), true);
            match (stmts, f.expression_body()) {
                (Some(s), _) => hw.walk_body(s),
                (None, Some(e)) => hw.walk_expression_body(e),
                _ => {}
            }
            let resolver = regs.iter().any(|r| matches!(r.method.as_str(), "QUERY" | "MUTATION" | "SUBSCRIPTION"));
            let pfacts: Vec<ParamFact> = f
                .params()
                .items
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    let mut decorators: Vec<String> = p.decorators.iter().map(|d| decorator_name(d, self.src).0).collect();
                    // `(parent, args, context, info)`: tag the roles like NestJS decorators do.
                    if resolver {
                        match i {
                            1 => decorators.push("Args".into()),
                            2 => decorators.push("GqlContext".into()),
                            _ => {}
                        }
                    }
                    ParamFact { name: p.pattern.get_identifier_name().map_or_else(|| "_".into(), |n| n.as_str().to_owned()), decorators }
                })
                .collect();
            let has_res = params.iter().any(|p| matches!(p.as_str(), "res" | "reply" | "response" | "resp"));
            let mk = |method: String, path: String, middleware: Vec<String>, location| HandlerFact {
                method,
                path,
                middleware,
                location,
                function: meta.name.clone(),
                params: pfacts.clone(),
                annotations: annotations.clone(),
                lookups: hw.out.lookups.clone(),
                derived: hw.out.derived.clone(),
                sinks: hw.out.sinks.clone(),
                body_paths: hw.out.body_paths.iter().cloned().collect(),
                has_response_param: has_res,
                defined_in: None,
                ineffective_middleware: vec![],
            };
            if regs.is_empty() && annotated_handler {
                self.handlers.push(mk("CALL".into(), meta.name.clone(), vec![], self.src.loc(span)));
            }
            if regs.is_empty() && handler_shaped {
                self.handler_bodies.push(mk(String::new(), String::new(), vec![], self.src.loc(span)));
            }
            for r in regs {
                self.handlers.push(mk(r.method.clone(), r.path.clone(), r.middleware.clone(), r.location.clone()));
            }
        }

        // Ledger?
        if let Some(s) = stmts
            && balance_writes(s)
        {
            self.ledger.push(LedgerFunctionFact {
                name: meta.name.clone(),
                params: params.clone(),
                exported,
                is_async: f.is_async(),
                location: self.src.loc(span),
                stmts: ledger_stmts(s, self.src, &aliases),
            });
        }
    }
}

impl<'a> Visit<'a> for P2<'_, '_> {
    fn visit_function(&mut self, f: &Function<'a>, flags: ScopeFlags) {
        if f.body.is_some() {
            self.process(FnRef::Func(f));
        }
        walk::walk_function(self, f, flags);
    }
    fn visit_arrow_function_expression(&mut self, a: &ArrowFunctionExpression<'a>) {
        self.process(FnRef::Arrow(a));
        walk::walk_arrow_function_expression(self, a);
    }
}

/// Resolve a relative import specifier against the importing file.
pub fn resolve_import(from_file: &str, spec: &str, known: &HashSet<String>) -> Option<String> {
    if !spec.starts_with("./") && !spec.starts_with("../") {
        return None;
    }
    let mut parts: Vec<&str> = from_file.split('/').collect();
    parts.pop();
    for seg in spec.split('/') {
        match seg {
            "." | "" => {}
            ".." => {
                parts.pop()?;
            }
            s => parts.push(s),
        }
    }
    let base = parts.join("/");
    let stem = base.trim_end_matches(".js").trim_end_matches(".mjs").trim_end_matches(".cjs").to_owned();
    let candidates = [
        base.clone(),
        format!("{stem}.ts"),
        format!("{stem}.tsx"),
        format!("{stem}.js"),
        format!("{stem}.jsx"),
        format!("{stem}.mjs"),
        format!("{stem}.cjs"),
        format!("{base}/index.ts"),
        format!("{base}/index.tsx"),
        format!("{base}/index.js"),
    ];
    candidates.into_iter().find(|c| known.contains(c))
}

pub fn analyze_program(program: &Program<'_>, src: &Source<'_>, known_files: &HashSet<String>) -> ModuleFacts {
    let mut p1 = P1 { src, st: Pass1::default(), stmt_start: 0 };
    p1.visit_program(program);
    let string_arrays = top_level_string_arrays(&program.body);
    let st = p1.st;
    let mut p2 = P2 {
        string_arrays: &string_arrays,
        src,
        p1: &st,
        comments: program.comments.as_slice(),
        functions: vec![],
        state_writes: vec![],
        handlers: vec![],
        handler_bodies: vec![],
        matched: Default::default(),
        ledger: vec![],
    };
    p2.visit_program(program);

    // Module-level code (initialisation, route wiring) as a pseudo-function.
    let aliases = collect_aliases(src, &program.body);
    let mut mw = Walker::new(src, &aliases, FnInfo { name: "<module>", params: &[], param_types: &[], exported: false, is_constructor: false }, false);
    mw.walk_body(&program.body);

    let P2 { functions, mut state_writes, handlers, handler_bodies, matched, ledger, .. } = p2;
    let route_refs: Vec<RouteRefFact> = st
        .handlers
        .iter()
        .enumerate()
        .filter(|(i, _)| !matched.contains(i))
        .filter_map(|(_, r)| match &r.target {
            HandlerTarget::Name(n) => Some(RouteRefFact {
                method: r.method.clone(),
                path: r.path.clone(),
                middleware: r.middleware.clone(),
                location: r.location.clone(),
                handler: n.clone(),
                args: r.args.clone(),
            }),
            HandlerTarget::Span(_) => None,
        })
        .collect();
    state_writes.extend(mw.out.state_writes);
    let imports = st.imports.iter().filter_map(|s| resolve_import(src.file, s, known_files)).collect::<BTreeSet<_>>().into_iter().collect();
    let mounts = st
        .mounts
        .iter()
        .map(|(prefix, mws, target, loc)| MountFact {
            prefix: prefix.clone(),
            middleware: mws.clone(),
            target_module: target.as_ref().and_then(|(t, _)| st.import_bindings.get(t)).and_then(|spec| resolve_import(src.file, spec, known_files)),
            target_text: target.as_ref().map(|(_, text)| text.clone()),
            location: loc.clone(),
        })
        .collect();
    let _ = idents; // re-exported helper used by detectors
    ModuleFacts {
        file: src.file.to_owned(),
        language: if src.file.ends_with(".ts") || src.file.ends_with(".tsx") || src.file.ends_with(".mts") || src.file.ends_with(".cts") {
            Lang::Typescript
        } else {
            Lang::Javascript
        },
        functions,
        routes: st.routes,
        enums: st.enums,
        tables: st.tables,
        state_writes,
        handlers,
        ledger_functions: ledger,
        imports,
        mounts,
        handler_bodies,
        route_refs,
        hash: proof_it_core::store::sha256_hex(src.text.as_bytes()),
    }
}
