# Validation: does Proof-It find what it claims?

All numbers below are reproducible from this repository.

## 1. Benchmarks (`benchmarks/`, `cargo test -p proof-it --test benchmarks`)

49 cases, each a minimal correct or broken implementation with the expected
status or finding: IDOR (unguarded, projection leak, missing `return`, scoped
query, tenant scoping, try/catch, swallowed throw, handler factory, trusted vs
header-copied identity), write IDOR, admin authorization (role checks, role
lists), ledger conservation/overdraft/floating point, state machines
(table, reopen, opaque guard, declared lifecycle), and SQLi/CMDi/SSRF/path
traversal/JWT/secrets with a false-positive check. **All pass.** Correct
implementations are PROVEN, broken ones VIOLATED (with Lean-certified
counterexamples), unmodelable ones UNPROVEN.

## 2. Recall on deliberately vulnerable applications

`benchmarks/real-world/manifest.yaml` lists each application's **published**
vulnerabilities at a pinned commit; `cargo test --release -p proof-it --test
real_world -- --ignored` clones, analyses (`--safe`) and scores them.

| Application | Detectable items found | Not detectable by design |
|---|---|---|
| OWASP NodeGoat | 13 / 13 | 3 (password policy, transport/at-rest encryption, admin-only route without code signal) + 1 needs network (dependencies) |
| DVNA | 11 / 11 | 2 (password-reset logic, logging practice) + 1 needs network |
| OWASP Juice Shop | 16 / 16 | 2 (runtime-generated REST endpoints, security-question reset) |
| nodejs-goof | 11 / 12 | 2 (container image library, ReDoS inside a dependency) + dependencies need network |
| DVWS-node | 23 / 23 | 6 (hidden API, JSON hijacking, XML-RPC enumeration, sensitive-field exposure, GraphQL batching, client-side template injection) |

**Honesty note.** Detectors were improved while looking at NodeGoat and DVNA,
so their scores overstate performance on unseen code. Juice Shop was used as a
**held-out** application: before any Juice-Shop-driven change Proof-It found
**9 / 16 (56%)** of its detectable items. The general fixes that followed
(destructured request sources, interprocedural taint into local helpers,
handler factories, middleware-provided identity, libxml2 XXE flags, NoSQL
update filters, zip slip, hash helpers) raised it to 16/16, after which Juice
Shop is no longer held-out. **56% is the first held-out estimate.**

A second held-out application, **DVWS-node** (`eb6e288`), was measured with the
ground truth written from its README *before* the first run, at repository
level (no file hints). First run, untuned: **9 / 23 detectable classes (39%)**.

*Scorer correction.* The recall harness originally checked only the first rule
of each item and ignored the pre-registered `any_of` alternatives. Re-scoring the untuned version with the corrected harness gives 10 / 23, but the
extra hit (JWT secret) came from a `SECRET-GENERIC` match inside the
challenge write-up (`CHALLENGES.md`), not from the committed `.env`. **We keep
9 / 23 (39%) as the honest untuned figure.**

Misses included classes Proof-It claims to cover (SSRF, XXE, CORS, IDOR, JWT
secrets) and classes it had no detector for. Each was traced to a general
cause and fixed without DVWS-specific rules:

| Miss | Cause | General fix |
|---|---|---|
| IDOR, vertical access | `router.route(p).get(mw, handler, guard.check(...))` chains not parsed; auth middleware (which sends 401s) chosen as the handler | route chains; ordered arguments; `(req, res, next)` bodies are middleware; guards registered *after* the handler are reported as protecting nothing |
| CORS, XXE | options passed by variable (`cors(corsOptions)`); Origin reflected by hand | option objects resolved file-wide; `Access-Control-Allow-Origin` set from the request |
| SSRF, GraphQL file write | XML-RPC method params and GraphQL resolver `args` were not sources | framework source models for RPC `(params, callback)` and resolvers `(parent, args, …)`; `fsPromise`-style receivers |
| JWT secret | unquoted, short value in a committed `.env` | dotenv credential rule; weak signing secrets reported as High |
| CRLF / log forging | request data pushed to an in-memory log store | log stores (`*Logs.push`, `logStream.write`, `appendFile(*.log)`) |
| XPath, XML/SOAP, introspection | no detector | `SEC-XPATH-INJECTION`, `SEC-XML-INJECTION` (taint through parsed request documents), `SEC-GRAPHQL-INTROSPECTION` |
| CSRF, brute force | cookie auth read by hand; route chains; limiter present but not on every credential check | manual cookie-auth signals; per-route check of password-verifying handlers |

After these changes DVWS-node scores **22 / 23** — no longer a held-out number.
The last miss, GraphQL resolver authorization, was closed later by modelling
`Query`/`Mutation` resolver maps as handlers (`args` = client input,
`context.user` = principal), plus two general walker fixes (lookups assigned
to an existing local or returned directly; presence tests such as
`typeof x === 'undefined'`). On a private production codebase these changed
no existing result and made four more handlers analysable. **The honest range for unseen code today is the two
untuned numbers: 56% and 39%.** The next held-out application will be measured
the same way before any change.

A third held-out application, **nodejs-goof** (`add14ba`), was measured the
same way: ground truth from its README and `exploits/` write-ups, committed before the first run. First run, untuned, offline (the dependency
item needs network and is not counted): **6 / 12 (50%)**. Hits: open redirect,
NoSQL injection, XSS, hard-coded session secret, server information
disclosure, prototype pollution. Misses: template render options from the
request body (layout file inclusion), shell injection, cookie without
`httpOnly`, insecure HTTP transport, plaintext password storage, zip slip.

Miss analysis and general fixes (no goof-specific rules):

| Miss | Cause | General fix |
|---|---|---|
| Shell injection | `url = item.match(re)[1]` dropped taint | taint through `match`/`matchAll` and `re.exec(x)` |
| Template file inclusion | `profile = req.body; res.render(view, profile)` | `SEC-SSTI`: the whole request object as template locals (client sets `layout`, ejs `settings`) |
| Plaintext passwords | `User.find({ password: req.body.password })` | `SEC-PLAINTEXT-PASSWORD`: query filters or SQL comparing the password column with a submitted value |
| Session cookie | `cookie: { path: '/' }` without `secure` | cookie options without `secure` are reported (the README's claim that `httpOnly` defaults to false is wrong for express-session; the real defect is `secure`) |
| Zip slip | `extractAllTo` of adm-zip **0.4.7** (CVE-2018-1002204) | reachable vulnerable dependency APIs: a vulnerable installed version **and** a call to the affected function (adm-zip, decompress, tar, lodash merge family) |
| Insecure HTTP | `http.createServer(app)` | not fixed: a plain-HTTP listener is normal behind a TLS-terminating proxy; a rule would fire on almost every service |

After these changes nodejs-goof scores 11 / 12 (tuned). The new rules also
found Juice Shop's documented local-file-read challenge (`...req.body` as
render locals in `dataErasure.ts`), which was missing from our Juice Shop
ground truth, and fired nothing on a private production codebase.

**Untuned held-out recall so far: 56%, 39%, 50%.**

## 3. Precision on a real codebase

Proof-It has been run read-only (`--safe`) on a private production codebase of
TypeScript and Go services. That is a spot check, **not a precision
measurement**:

- Early runs produced mostly false positives for object-level authorization
  (pagination parameters treated as identifiers, try/catch checks ignored,
  router mounts, tenant scoping). Each cause was fixed in general and covered
  by a benchmark.
- Its results there have not all been triaged, and some reported violations
  are deliberate design choices that need suppressions with reasons. Until a
  full triage is done, Proof-It has **no measured false-positive rate on real
  code**.

## 4. Independent measurement and audit (read this before trusting the numbers above)

The recall figures in section 2 are scored per repository: one finding of the
right rule anywhere counts. An adversarial audit of Proof-It found that this
flatters it, and found worse:

- **Per-file recall is low.** OWASP Juice Shop ships, for each coding
  challenge, several vulnerable variants and the official fix. Measured per
  file, Proof-It flagged **20 of 67 vulnerable variants (30%)**. Some misses are
  fragments that do not parse or are out of scope (prompt injection, web3), but
  many are in scope (login SQL injection variants, open-redirect allow-list
  bypasses, frontend XSS). It flagged 6 of the 25 official fixes, mostly for
  unrelated issues in the same snippet.
- **It could be gamed by names (fixed).** A middleware `requireAdmin = (req,
  res, next) => next()` produced a kernel-checked PROVEN: the generated theorem
  was `A ∧ True → A`, because the extractor assumed the conclusion from the
  name. A `sanitizeInput` that returned its input cleared taint. Guards and
  sanitizers are now judged by their code, and a result that follows from
  Proof-It's assumptions alone is never PROVEN (`proven_requires_code` in the
  Lean specification). Permanent benchmarks cover each trick.
- **It passed code it never read (fixed).** A file that failed to parse gave
  "ASSURANCE: PASSED". Unanalysed source files now make a run INCOMPLETE.

What remains true: detection is mostly patterns over a syntax tree, taint is
module-local, only TypeScript/JavaScript (fully) and Go (security analysis,
not yet measured on a held-out application) are supported, and recall on unseen
code is somewhere between 30% and 56% depending on how you count.

## 5. Self-assurance


- `lean/ProofIt/Models/Assurance.lean`: kernel-checked theorems about
  Proof-It's own status classification and merge decision; the Rust
  implementation is checked against Lean's evaluation on all inputs.
- Model self-check: every PROVEN obligation is re-checked by the independent
  evaluator; a disagreement turns the result into ERROR.
- Mutation testing (`proof-it test --mutate`): on the demo project 17/28
  injected bugs change the assurance result; survivors are reported (they
  reveal missing properties, e.g. "only admins may reopen").

## What these numbers do not say

They do not say Proof-It finds every vulnerability, nor that a PASSED run
means secure software. They measure detection of known, code-visible
vulnerability classes on a small set of applications.
