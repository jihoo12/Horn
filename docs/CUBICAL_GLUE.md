# Fresh Glue evidence

```sh
cargo run --release --locked --offline --bin horn -- cubical run examples/cubical/source/glue.hcu
```

The core source accepts `(glue-type BASE_TYPE FACE PARTIAL_TYPE EQUIVALENCE)`,
`(glue GLUE_TYPE PARTIAL_VALUE BASE_VALUE)` and `(unglue VALUE)`.
None introduces a binder. GLUE_TYPE must elaborate to literal `glue-type`
syntax in this subset. Unlike a pair annotation, this type argument is part
of the existing object term and remains in the certificate.

On ambient face `psi`, formation checks BASE_TYPE at a universe, the
attaching FACE, PARTIAL_TYPE at the SAME universe on `psi ∧ FACE`, the
certified expansion of `equiv PARTIAL_TYPE BASE_TYPE`, its universe and the
equivalence witness on that intersection. An ordinary function alone is
insufficient. Creation then checks PARTIAL_VALUE on the intersection,
BASE_VALUE on all of `psi`, the mapped value `(app (fst EQUIVALENCE)
PARTIAL_VALUE)` and its equality to BASE_VALUE on the intersection. Every
premise is emitted for the unchanged `rhas.glue-type`/`rhas.glue` rules.

```text
(check make (scope () ((e (equiv nat nat))))
  (glue (glue-type nat ft nat e) zero (app (fst e) zero))
  (glue-type nat ft nat e))
(equal beta (scope () ((e (equiv nat nat))))
  (unglue (glue (glue-type nat ft nat e) zero (app (fst e) zero)))
  (app (fst e) zero) nat)
```

The equivalence in this example is a context hypothesis, not a new axiom or
a freshly generated identity-equivalence proof. The closed empty-face example
uses typed empty systems instead: no equivalence inhabitant is needed on
that face. False elimination is not used to admit ill-typed or unscoped
expressions.

`unglue` infers the base type. Its beta equation returns a literal Glue's
BASE_VALUE. When `psi` entails FACE, the producer certifies that implication
and supports Glue type reduction, Glue value reduction and unglue's face
equation through the equivalence's function. Reconstruction eta checks both
the original and reconstructed Glue values. Converting a value or equation
to the partial type uses explicit `rhas.conv`/`req.conv`; the attaching face
must cover the requested ambient face. Partial judgments cannot escape as
global ones. All four ordinary/dimension operations are certified; only
dimension operations transform the attaching face.

Glue syntax anywhere in the request, including contexts, macro arguments and
erased annotations, selects `Profile::Glue`, exactly the existing first nine
fragments through `glue.horn`. Equivalence abbreviations are lowered with
checked definition facts before core inference. The profile includes neither
the later equality/congruence fragment nor type-directed composition rules.
Export contains this exact theory for independent generic-kernel replay.
The kernel, object theories, dependencies and Agda models are unchanged.

This is bounded Glue typing and beta/face/eta evidence. It does not implement
Glue-directed composition or fresh ua/univalence generation. General
congruence and dependent transport are still absent: for example a function
component `(fst (pair ...))` is not reduced underneath `app` in this profile.
Choose a base whose boundary compatibility is provable by the supported
rules. Failure to find evidence is not a mathematical counterexample. The
existing source, expansion, conversion, face-search and proof-size bounds
still apply; semantic adequacy and executable-to-Agda refinement are separate
obligations.
