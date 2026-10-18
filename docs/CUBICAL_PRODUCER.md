# Fresh path-theory certificate generation

`cubical::producer::produce` constructs new certificates from typed requests.
It does not load the frozen univalence oracles or use kamo3 at runtime. It
uses only the existing `theories/cubical/path.horn` fragment, an explicit
subset of the full cubical package, and changes no rules or kernel code.


## Core source files

```sh
cargo run --release --locked --offline --bin horn -- cubical run examples/cubical/source/basics.hcu
cargo run --release --locked --offline --bin horn -- cubical run examples/cubical/source/binders.hcu --emit /tmp/horn-fresh
cargo run --release --locked --offline --bin kernel -- /tmp/horn-fresh/theory.horn /tmp/horn-fresh/goals /tmp/horn-fresh/proof
```

`--emit` requires a new directory and writes only after successful generation
and kernel checking. Exported data can be replayed independently. The generated
certificate contains ordinary steps, not a reference to a frozen demonstration.

```text
(check identity (lam nat (v 0)) (pi nat nat))
(equal beta (app (lam nat (v 0)) zero) zero nat)
(check constant-path (plam nat zero) (path nat zero zero))
(equal path-beta (scope 1 ()) (papp (plam nat zero) (dim 0)) zero nat)
```

Assertions are `(check NAME [SCOPE] TERM TYPE)` and
`(equal NAME [SCOPE] LEFT RIGHT TYPE)`. The optional scope is
`(scope DIMENSIONS (CONTEXT-TYPES...))`; its default is `(scope 0 ())`.
Each name must be unique. Contexts are oldest first. `;` begins a comment.
Levels and indices are written as decimal naturals and elaborated to the
existing unary object syntax. `v 0` denotes the latest ordinary binder and
`dim 0` the latest dimension binder. Explicit annotations make the core small:
`(lam DOMAIN BODY)` binds an ordinary variable, `(pi DOMAIN CODOMAIN)` binds
one in its codomain, `(plam FAMILY BODY)` binds a dimension in both family and
body, and `(path FAMILY LEFT RIGHT)` binds a dimension in its family only.
`(papp PATH INTERVAL)` applies a path. Intervals are `i0`, `i1`, `(dim N)`,
`(neg R)`, `(meet R S)` and `(join R S)`.

This is an explicit core input format, not the final named-binder surface
language. Source files cannot declare rules, axioms or theories. The `.hn`
programming frontend and `.hcu` cubical frontend are not yet one source language.
The source-to-core translation has no formal correctness proof; generic checking
establishes the fixed elaborated judgments relative to the selected rules.

## Producer API and supported reasoning

The annotated `Term` API supports universes, variables, Nat/zero, dependent
products, annotated lambdas, application, dependent paths, annotated path
lambdas and path application. Lambda domain and path-lambda family annotations
are source metadata, erased from object terms. Their typing obligations are
still derived. Context types are oldest first at their binding sites;
ordinary and dimension variables have independent de Bruijn indices.

Each `Request` fixes a name, dimension scope, context, term(s) and expected
type. Both typing and equality goals are fixed from those inputs. The producer
cannot change a goal to its inferred answer. Every arithmetic comparison,
context lookup, shift, substitution and typing step becomes an ordinary Horn
rule application. Both kinds of substitution respect both kinds of binder.
The result is returned only after the ground kernel checks all evidence.

Equality generation currently supports reflexivity and chains of root beta,
path beta and path endpoint reductions, with symmetry and transitivity. Type
checking requires syntactically matching inferred/expected object types; it
has no general conversion search. A failure to generate evidence is not a
proof that the statement is false.

The producer has resource limits: 128 requests, 32 context variables or
free dimensions, input indices/levels at most 32, syntax depth 32 and 10,000
nodes per request, 50,000 generated steps per run, and 32 root reductions per
side of an equality. These bounds describe the implementation, not the theory.
The public syntax validator checks these before recursive quotation/inference.

Tests construct fresh identities at several universe levels, beta/path
computations, scoped endpoint laws, substitutions under both binder kinds
and dimension-dependent contexts. They independently replay emitted evidence
and reject wrong types, free variables/dimensions, bad context entries,
changed goals and invented rule names. This is not a complete cubical
elaborator or a proof of semantic soundness. Face systems, composition, Glue
and fresh univalence generation remain later migration stages.
