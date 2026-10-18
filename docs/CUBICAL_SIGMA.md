# Dependent pairs in fresh source

```sh
cargo run --release --locked --offline --bin horn -- cubical run examples/cubical/source/sigma.hcu
```

`(sigma DOMAIN BODY)` and `(sigma NAME DOMAIN BODY)` bind an ordinary variable
in BODY. A pair is `(pair SIGMA_TYPE FIRST SECOND)`; its annotation is source
metadata and must be a literal Sigma type in this subset. The annotation is
erased from the object term, but both type fields and both components are
checked. The second component is checked against BODY with FIRST substituted.
`(fst PAIR)` and `(snd PAIR)` infer their types, exposing a reducible Sigma head
with explicit conversion evidence when needed.

```text
(check dependent (pair (sigma A (u 0) A) nat zero) (sigma A (u 0) A))
(equal projection (snd (pair (sigma A (u 0) A) nat zero)) zero nat)
(equal eta (scope () ((p (sigma A (u 0) A))))
  (pair (sigma A (u 0) A) (fst p) (snd p)) p (sigma A (u 0) A))
```

The natural type of `snd p` is BODY with `fst p` substituted, including when
p is a literal pair. It is not silently replaced with BODY[FIRST]. The
existing `req.snd-beta` checks its output at that natural type. To use the
equality at another convertible type, `req.conv` certifies the type equality
and the well-formed destination type. For the example above, the natural type
is `fst (pair nat zero)`; the producer certifies its equality with Nat.
First projection beta and pair eta use `req.fst-beta` and `req.pair-eta`.
Reflexivity/eta still check all annotations, even when quoting erases them.

All typing is derived with the unchanged `rhas.sigma`, `rhas.pair`,
`rhas.fst` and `rhas.snd` rules. Global results use `ft` export. Local pair
components may rely on the requested face; those casts cannot escape it.
The pair types participate in context lookup and both ordinary/dimension
substitutions. Ordinary substitution lifts its argument under a Sigma binder;
dimension operations do not treat that binder as a dimension.

Sigma syntax anywhere in input, including erased annotations and context
types, selects `Profile::Sigma`: the existing first seven theory fragments.
The selected theory includes composition but no equivalence/Glue axioms or
rules. Earlier constructs retain their smaller profiles. Export contains
the selected theory for independent generic-kernel replay. No trusted kernel,
object theory or Agda model was changed.

This remains bounded root computation, not complete definitional equality.
There is no general Sigma/pair/projection congruence search, no Sigma-directed
composition reduction and no universe cumulativity. Pair annotation heads
must be literal Sigma syntax; arbitrary convertible annotations are not
inferred. Source, conversion, face-search and proof-size bounds still apply.
Equivalence definitions and fresh Glue/ua production are separate increments.
