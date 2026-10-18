# Fresh cubical certificate generation

`cubical::producer::produce` constructs new certificates from typed requests.
It does not load the frozen univalence oracles or use kamo3 at runtime. It
uses the existing scoped-path fragment by default. Face assertions select
the fixed path-plus-faces profile, while systems/restricted assertions select
the five-fragment systems profile; see [face and system evidence](CUBICAL_FACES_SYSTEMS.md).
Composition anywhere in the input selects the six-fragment composition profile;
see [composition evidence](CUBICAL_COMPOSITION.md).
No rules or kernel code are changed. Replay fresh output with its returned
`Generated.theory`, which is also written by CLI export.


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

Named forms are also accepted:

```text
(check id (lam A (u 0) (lam x A x)) (pi A (u 0) (pi x A A)))
(equal beta (app (lam x nat x) zero) zero nat)
(equal path-beta (scope (i) ()) (papp (plam j nat zero) i) zero nat)
```

`(lam NAME DOMAIN BODY)` and `(pi NAME DOMAIN CODOMAIN)` bind an ordinary
name in the body/codomain only. `(plam NAME FAMILY BODY)` binds a dimension
in both family and body. `(path NAME FAMILY LEFT RIGHT)` binds a dimension
in the family only. Bare term names and interval names resolve in separate
namespaces, to the nearest binder. Anonymous forms still introduce binders,
so mixing named forms with index forms does not capture outer names.

A named scope is `(scope (DIMENSION-NAMES...) ((NAME TYPE)...))`. Both lists
are oldest first. Each context type can refer to earlier context names and
the dimension names, but not to its own name or later context entries. Names
within either scope list must be distinct; local binders may shadow them.
Binder names start with an ASCII letter or `_`, followed by ASCII letters,
digits, `_`, `-`, `.` or `'`; built-in syntax/constant names are reserved.
See [named.hcu](../examples/cubical/source/named.hcu).

This remains a small prefix source format with explicit annotations. Source files cannot declare rules, axioms or theories. The `.hn`
programming frontend and `.hcu` cubical frontend are not yet one source language.
The source-to-core translation has no formal correctness proof; generic checking
establishes the fixed elaborated judgments relative to the selected rules.

## Producer API and supported reasoning

The annotated `Term` API supports universes, variables, Nat/zero, dependent
products, annotated lambdas, application, dependent paths, annotated path
lambdas, path application, annotated coherent systems and composition. Lambda domain,
path-lambda family and system type annotations
are source metadata, erased from object terms. Their typing obligations are
still derived. Context types are oldest first at their binding sites;
ordinary and dimension variables have independent de Bruijn indices.

Each `Request` fixes a name, dimension scope, context, term(s) and expected
type. Both typing and equality goals are fixed from those inputs. The producer
cannot change a goal to its inferred answer. Every arithmetic comparison,
context lookup, shift, substitution and typing step becomes an ordinary Horn
rule application. Both kinds of substitution respect both kinds of binder.
The result is returned only after the ground kernel checks all evidence.

Equality generation supports reflexivity and chains of root beta, path beta
and path endpoint reductions, with symmetry and transitivity. Type checking
first compares inferred/expected types syntactically. If they differ, it now
constructs equality evidence in their common universe, checks the destination
type and applies the existing `type.conv` rule. Reducible function, path and
universe heads are exposed with the same explicit typing conversion. Requested
goals retain their original types; the producer does not replace them with
normalized goals. See [conversion.hcu](../examples/cubical/source/conversion.hcu).

This is bounded root conversion, not full definitional equality. There is no
reduction under arbitrary constructors or binders, no Pi/lambda congruence
search and no universe cumulativity. The small path theory has `type.conv` but
no general `eq.conv` rule: a non-reflexive reduction at a converted equality
type is reported as unsupported rather than silently retyping the equality.
Reflexivity still checks both annotated operands before emitting evidence.
A failure to generate evidence is not a proof that the statement is false.

The producer has resource limits: 128 requests, 32 context variables or
free dimensions, input indices/levels at most 32, syntax depth 32 and 10,000
nodes per request, 50,000 generated steps per run, and 32 root reductions per
side of an equality, and 32 nested conversion obligations. These bounds
describe the implementation, not the theory.
The public syntax validator checks these before recursive quotation/inference.

Tests construct fresh identities at several universe levels, beta/path
computations, scoped endpoint laws, substitutions under both binder kinds
and dimension-dependent contexts. They independently replay emitted evidence
and reject wrong types, free variables/dimensions, bad context entries,
changed goals and invented rule names. This is not a complete cubical
elaborator or a proof of semantic soundness. A bounded face/system generator is described in [its guide](CUBICAL_FACES_SYSTEMS.md).
Native restricted inference and local type/equality conversion now use the
existing restricted rules; see the face/system guide and restricted.hcu.
Composition typing and active-face computation now have a fixed six-fragment
profile; see [CUBICAL_COMPOSITION.md](CUBICAL_COMPOSITION.md). General congruence,
type-directed composition, Glue and fresh univalence generation remain later
migration stages.
