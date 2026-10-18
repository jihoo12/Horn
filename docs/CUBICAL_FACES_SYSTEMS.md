# Face evidence and systems

## Face source assertions

```sh
cargo run --release --locked --offline --bin horn -- cubical run examples/cubical/source/faces.hcu
```

The existing `.hcu` scope syntax is shared with terms. Face literals are
`ff`, `ft`, `(at0 DIMENSION)` and `(at1 DIMENSION)`; dimensions can be decimal
indices or names in the dimension namespace. Compound faces are `(fand A B)`
and `(for A B)`.

```text
(entails weaken (scope (i j) ()) (at0 i) (for (at0 i) (at1 j)))
(local endpoint (scope (i) ()) (at0 i) i i0)
(local meet-endpoint (scope (i j) ()) (at0 i) (meet i j) i0)
```

`entails` fixes a face implication goal. The producer certifies scope, each
list extraction and every branch of a sequent proof using the unchanged
`cover`/`entails.checked` rules. It does not assert a truth-table result as
an oracle. In particular `ft → (i=0 ∨ i=1)` is rejected: a generic dimension
need not be either endpoint.

`local` fixes interval equality on a face. The current generator supports
reflexivity, certified endpoint boundaries, structural congruence, and two
expressions sharing an endpoint on the face. This is not a complete interval
algebra decision procedure. False faces still require both expressions and
all face dimensions to be in scope.

Successful evidence is checked by the unchanged ground kernel. A separate
test compares 160 implications over two dimensions with all nine partial
assignments, including unspecified dimensions; this is finite test coverage,
not a universal soundness proof.

## Theory selection and limits

Fresh output now carries `Generated.profile` and `Generated.theory`. Path-only
requests retain the scoped-path profile. Face assertions select the fixed
path-plus-faces profile. Callers must replay with the returned theory; the
legacy `producer::THEORY` constant denotes only the path fragment. CLI export
writes the actual selected theory, goals and proof, and still requires a new
directory. Source files cannot declare arbitrary rules or axioms.

The source bounds remain in force. Face proof search additionally has limits
of 128 recursive cover frames and 20,000 cover obligations per run, alongside
the shared 50,000 emitted-step limit. A search limit is not a mathematical
counterexample. Object-theory adequacy, executable/kernel refinement and
source elaboration correctness remain separate obligations.
