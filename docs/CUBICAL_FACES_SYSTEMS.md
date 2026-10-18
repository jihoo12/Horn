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

## Coherent systems

```sh
cargo run --release --locked --offline --bin horn -- cubical run examples/cubical/source/systems.hcu
```

A system is `(system TYPE ((FACE TERM)...))`. Its type annotation is source
metadata; the object term is the existing `system`/`side`/`snil` syntax.
Ordinary `check`/`equal` requests mean global judgments. Restricted requests
are `(check-on NAME [SCOPE] FACE TERM TYPE)` and
`(equal-on NAME [SCOPE] FACE LEFT RIGHT TYPE)`.

```text
(check full (system nat ((ft zero))) nat)
(check-on partial (scope (i) ()) (for (at0 i) (at1 i))
  (system nat (((at0 i) zero) ((at1 i) zero))) nat)
(equal-on endpoint (scope (i) ((p (path nat zero zero))))
  (at0 i) (papp p i) zero nat)
```

For each system the generator certifies every face, each branch's typing on
the intersection with the requested base, every pairwise overlap equality,
and that the union of branch faces covers the base. Checking only adjacent
branches would be insufficient; a three-branch rejection test targets that
mistake. Disjoint branches may differ because their contradictory overlap is
certified with `req.false`, after both terms have been typed.

The first supported subset uses globally typed contexts/types/branch terms,
plus recursively checked system branches. It embeds those typings with
`rhas.global`. It does not implement general restricted type inference or
face-dependent type conversion, and does not use false elimination to admit
ill-typed or unscoped branch terms. Matching path applications can be related
by certified local interval equality when the family instances and requested
type are syntactically identical. Path endpoint equations then yield local
branch agreement. Reflexivity, supported global equations, false overlaps,
cases and system agreement are explicit rule applications.

A partial result remains an `rhas` or `req` goal with its face. No global
export is performed unless the existing `ft` export rule is applicable.
For example the two endpoint faces do not cover the whole interval, so
replacing the `check-on` above with a global `check` is rejected. The tests
also forge an `rhas.export` step from a partial result and require the generic
kernel to reject it. An empty system is supported on `ff`, not on `ft`.

Globally active branches can reduce a full system with
`req.system-branch` followed by `req.export`. Agreement of all branches with
a target on a partial base uses `agrees` and `req.system-eq`. All four
ordinary/dimension shifts/substitutions for systems are certified; dimension
operations transform faces too. Substituting a compound interval into a face
literal uses its certified endpoint boundary, not Boolean negation.

Systems and restricted assertions select `Profile::Systems`, comprising the
existing path, faces, face-ops, restricted and systems fragments. Composition,
Sigma, Glue and their rules are not included in this fresh profile. Source
selection is based on the requested constructs before evidence generation;
a certificate cannot install rules. `Generated.theory` and CLI export expose
the actual specification used. Input systems have at most 16 branches each;
restricted equality search has a depth limit of 64 in addition to shared
source, face-search and emitted-step limits. General conversion, composition
and Glue generation remain later steps.
