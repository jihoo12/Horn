# Explicit equality profile and checked inner computation

```sh
cargo run --release --locked --offline --bin horn -- cubical run examples/cubical/source/congruence-heads.hcu --profile equality
```

`--profile equality` selects exactly the existing first ten theory fragments,
through `equality.horn`. It includes Glue but excludes canonical-map and
computation extensions. Source cannot install rules or axioms. Without the
option, the previous automatic, smaller profiles are preserved. An explicitly
chosen smaller profile is rejected if the request needs a later fragment.
Other fixed names are path, faces, systems, composition, sigma, equivalence
and glue. Unknown names and duplicate/missing options fail before export.
`--profile` and `--emit NEW_DIR` may appear in either order; export still
requires a new directory and includes the exact selected theory.

Rust callers use `source::run_with_profile` or
`producer::produce_with_profile(requests, Profile::Equality)`. Goals remain
fixed by the caller. The equality-profile request boundary exports restricted
typing/equality evidence only at `ft`; partial source assertions retain their
faces. This avoids pretending that a type-level reduction or local equation
can silently change a requested global judgment.

The current generator certifies reduction in function/argument positions,
first/second projections, path application and unglue. Each congruence step
uses an existing `req.*-cong` rule and rechecks BOTH whole terms at the rule's
exact output type. For dependent application that type is B[OLD_ARGUMENT];
for dependent second projection it is B[fst OLD_PAIR]. A change to the
requested equality type requires explicit `req.conv` evidence. No dependent
result types are identified implicitly.

```text
(equal computed
  (app (fst (pair (sigma f (pi nat nat) nat) (lam x nat x) zero)) zero)
  zero nat)
```

The example needs `req.app-cong` to reduce the projected function, followed
by the ordinary typed beta rule. This also lets Glue boundary compatibility
compute a function projected from an explicitly supplied equivalence pair.
It does not generate the pair's isEquiv witness. Earlier profiles continue
to report this inner computation as unsupported.

All existing input, conversion, face-search and proof-step limits apply.
Recursive reduction additionally has a 64-frame guard, restored after failed
attempts; evidence reuse happens only after checking both annotated operands.
This is bounded proof search, not complete definitional equality. Binder
congruence, stronger dependent transport, type-directed composition and fresh
ua/univalence generation remain separate increments. No kernel, object theory,
Agda model or dependency changed.
