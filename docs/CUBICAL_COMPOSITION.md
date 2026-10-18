# Fresh composition certificates

```sh
cargo run --release --locked --offline --bin horn -- cubical run examples/cubical/source/composition.hcu
```

The annotated core accepts `(comp FAMILY FACE TUBE BASE)` and
`(comp NAME FAMILY FACE TUBE BASE)`. A fresh dimension is in scope in FAMILY
and TUBE only. FACE and BASE use the outer dimension namespace, even when
NAME shadows an outer name. Anonymous composition also counts as a binder for
numeric indices. Ordinary and dimension variables remain independent.

```text
(check partial-tube (scope (i) ())
  (comp k nat (at0 i) (system nat (((at0 i) zero))) zero) nat)
(equal-on boundary (scope (i) ()) (at0 i)
  (comp k nat (at0 i) (system nat (((at0 i) zero))) zero) zero nat)
(check empty-tube (comp k nat ff (system nat ()) zero) nat)
```

For an ambient face `psi`, the generator certifies the restricted context,
its dimension shift, both face shifts, the universe of the whole family,
tube typing on `psi ∧ FACE` in the extended cube, both endpoint family types,
BASE at the zero endpoint, and equality of the zero tube endpoint with BASE
on `psi ∧ FACE`. The result has the family's one-endpoint type. Each premise
is an explicit application of the unchanged `rhas.comp` rule. Partial tubes
are checked as partial systems; they need not have global typing.

When `psi` entails FACE, the generator certifies that implication, substitutes
one into TUBE, checks its type and emits `req.comp-face`. A global assertion
uses `psi=ft` and the existing export rule. Equations in the composition
profile use restricted evidence and explicit `req.conv` when a step's natural
type differs from the requested type. Nothing implicitly identifies
convertible equality types. Every ordinary/dimension shift/substitution of
composition is certified, including lifting a substituted ordinary argument
across its new dimension binder and transforming its outer face.

Composition syntax anywhere in the request, including erased annotations and
context types, selects `Profile::Composition`: exactly the first six existing
fragments through `composition.horn`. It adds no Glue, equivalence, equality
extension or type-directed computation rules. Path-only and system-only
requests retain their smaller profiles. Export includes the selected theory
and can be checked with the independent generic `kernel` executable.

This is composition typing and active-face computation, not a complete
Kan operation evaluator. There is no regularity equation identifying an
empty-face composition with BASE. Nat/Pi/Sigma/Path/Glue/universe-directed
composition reduction, general congruence, fresh ua/univalence evidence
and connection to the `.hn` frontend remain future work. Unsupported proof
search is rejected; it is not a counterexample. All source, face-search,
conversion, restricted-equality and emitted-step bounds remain in force.
The unchanged object theory's semantic adequacy is a separate obligation
from checking certificates against that theory.

[Fresh Glue typing and beta/face/eta evidence](CUBICAL_GLUE.md) now use a
separate fixed profile; Glue-directed composition is still outside this
composition subset.
