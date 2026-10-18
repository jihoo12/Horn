# Fresh path-theory certificate generation

`cubical::producer::produce` constructs new certificates from typed requests.
It does not load the frozen univalence oracles or use kamo3 at runtime. It
uses only the existing `theories/cubical/path.horn` fragment, an explicit
subset of the full cubical package, and changes no rules or kernel code.

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
