//! Go adapter (tree-sitter-go).
//!
//! Produces the language-neutral facts Proof-It's formal layer consumes and
//! Go-specific security findings. Purely syntactic: no type checker, no package
//! resolution, no execution. Request sources are recognised by the declared type
//! of handler parameters (`*http.Request`, `*gin.Context`, `echo.Context`,
//! `*fiber.Ctx`), not by variable names.
//!
//! Not yet produced for Go: route/handler facts for the authorization models
//! (AUTHZ-*), state machines and ledgers. Runs that contain Go say so.

mod detect;
mod taint;

use proof_it_core::facts::{FunctionFact, Language, ModuleAnalysis, ModuleFacts};
use proof_it_core::types::SourceLocation;
use tree_sitter::{Node, Parser, Tree};

/// Parse `text` (repository-relative `file`) and extract facts and findings.
pub fn analyze(file: &str, text: &str) -> Result<ModuleAnalysis, String> {
    let tree = parse(text)?;
    let src = Src { file, text };
    if let Some(e) = first_error(tree.root_node()) {
        let (line, col) = (e.start_position().row + 1, e.start_position().column + 1);
        return Err(format!("syntax error at {line}:{col}"));
    }
    let root = tree.root_node();
    let functions = functions(&src, root);
    let findings = detect::run(&src, root);
    let facts = ModuleFacts {
        file: file.to_owned(),
        language: Language::Go,
        functions,
        routes: vec![],
        enums: vec![],
        tables: vec![],
        state_writes: vec![],
        handlers: vec![],
        ledger_functions: vec![],
        imports: vec![],
        mounts: vec![],
        handler_bodies: vec![],
        route_refs: vec![],
        hash: proof_it_core::store::sha256_hex(text.as_bytes()),
    };
    Ok(ModuleAnalysis { facts, findings, text: text.to_owned() })
}

fn parse(text: &str) -> Result<Tree, String> {
    let mut p = Parser::new();
    p.set_language(&tree_sitter_go::LANGUAGE.into()).map_err(|e| e.to_string())?;
    p.parse(text, None).ok_or_else(|| "parser returned no tree".to_owned())
}

/// The first ERROR or MISSING node: a recovered parse is a partial program,
/// and analysing it as if complete would hide whatever the parser dropped.
fn first_error(n: Node<'_>) -> Option<Node<'_>> {
    if n.is_error() || n.is_missing() {
        return Some(n);
    }
    if !n.has_error() {
        return None;
    }
    let mut c = n.walk();
    n.children(&mut c).find_map(first_error)
}

/// Source text helpers shared by the analyses.
pub(crate) struct Src<'s> {
    pub file: &'s str,
    pub text: &'s str,
}

impl<'s> Src<'s> {
    pub fn of(&self, n: Node<'_>) -> &'s str {
        self.text.get(n.byte_range()).unwrap_or("")
    }
    /// Node text with all whitespace removed (for matching callees like `r.URL.Query().Get`).
    pub fn compact(&self, n: Node<'_>) -> String {
        self.of(n).split_whitespace().collect()
    }
    pub fn loc(&self, n: Node<'_>) -> SourceLocation {
        let line = n.start_position().row + 1;
        let snippet: String = self.text.lines().nth(line - 1).unwrap_or("").trim().chars().take(200).collect();
        SourceLocation {
            file: self.file.to_owned(),
            line: u32::try_from(line).unwrap_or(u32::MAX),
            column: u32::try_from(n.start_position().column + 1).ok(),
            end_line: u32::try_from(n.end_position().row + 1).ok(),
            snippet: Some(snippet),
        }
    }
}

/// Every node of `kind` below `n` (pre-order).
pub(crate) fn descendants<'t>(n: Node<'t>, kind: &str) -> Vec<Node<'t>> {
    let mut out = Vec::new();
    let mut stack = vec![n];
    while let Some(x) = stack.pop() {
        if x.kind() == kind {
            out.push(x);
        }
        let mut c = x.walk();
        let kids: Vec<Node<'t>> = x.children(&mut c).collect();
        stack.extend(kids.into_iter().rev());
    }
    out
}

fn functions(src: &Src<'_>, root: Node<'_>) -> Vec<FunctionFact> {
    let mut out = Vec::new();
    for kind in ["function_declaration", "method_declaration"] {
        for f in descendants(root, kind) {
            let name = f.child_by_field_name("name").map(|n| src.of(n).to_owned()).unwrap_or_default();
            let params = f.child_by_field_name("parameters").map(|p| taint::param_names(src, p)).unwrap_or_default();
            let statements = f.child_by_field_name("body").map_or(0, |b| descendants(b, "statement_list").first().map_or(0, Node::named_child_count));
            out.push(FunctionFact {
                exported: name.starts_with(|c: char| c.is_ascii_uppercase()),
                name,
                params,
                location: src.loc(f),
                is_async: false,
                statements,
                annotations: vec![],
                request_overrides: vec![],
                guard: None,
                admits_roles: None,
            });
        }
    }
    out
}
