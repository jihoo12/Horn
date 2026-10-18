# Certified equivalence definitions

```sh
cargo run --release --locked --offline --bin horn -- cubical run examples/cubical/source/equivalence.hcu
```

Fresh source accepts four type abbreviations:

| Source | Definition |
| --- | --- |
| `(contr X)` | `Sigma c:X. Pi x:X. Path X c x` |
| `(fiber A B f y)` | `Sigma a:A. Path B (f a) y` |
| `(isequiv A B f)` | `Pi y:B. contr (fiber A B f y)` |
| `(equiv A B)` | `Sigma f:(A -> B). isequiv A B f` |

These are the existing `equivalence-defs.horn` definitions, not new object
constructors or isEquiv axioms. They elaborate to Pi/Sigma/Path terms before
core inference. Every ordinary/dimension lift in an expansion is certified,
and every expansion emits the matching `def.contr`, `def.fiber`,
`def.isequiv` or `def.equiv` fact. The generic checker checks those steps,
including expansions used only in erased annotations. Typing then checks
the resulting ordinary core terms with the existing rules.

```text
(check formation (equiv nat nat) (u 0))
(check forward (scope () ((e (equiv nat nat)))) (app (fst e) zero) nat)
(check supplied-witness (scope () ((w (isequiv nat nat (lam x nat x)))))
  (pair (equiv nat nat) (lam x nat x) w) (equiv nat nat))
```

Formation of `equiv A B` does not supply an inhabitant of it. The last example
uses a witness explicitly declared in its context. A function by itself, or
a pair with an unrelated second component, is rejected as an equivalence.
This increment does not generate a contraction proof for arbitrary fibers,
a fresh identity equivalence proof, ua or univalence. Glue typing uses these
definitions in the [separate Glue profile](CUBICAL_GLUE.md).

`(expand NAME [SCOPE] DEFINITION EXPECTED)` fixes a definition-expansion goal:

```text
(expand fiber-expansion (fiber nat nat (lam x nat x) zero)
  (sigma a nat (path nat (app (lam x nat x) a) zero)))
(expand equiv-expansion (equiv nat nat)
  (sigma f (pi a nat nat) (isequiv nat nat f)))
```

EXPECTED may contain abbreviations too. It is elaborated independently and
must match the specified expansion syntactically after annotation erasure;
the producer cannot replace it with its inferred answer. The object `*def`
predicate describes syntax, not an equivalence witness or a typing judgment.
The source `expand` assertion separately checks its context and type/function/
fiber-endpoint arguments and the EXPECTED type globally, including its erased
annotations. Use `check` to request formation evidence as an explicit goal,
and `check-on` for a type whose formation depends on a face. Abbreviations
inside restricted assertions use the same lowering, followed by local typing.

Any abbreviation or expand assertion selects `Profile::Equivalence`, exactly
the existing first eight fragments through `equivalence-defs.horn`. Contexts
and erased annotations participate in selection. Output has no macro term
constructors; CLI export includes the actual selected theory and can be
replayed by the independent `kernel` executable. Earlier inputs retain their
smaller profiles. The kernel, object theories and Agda models are unchanged.

Both input and every intermediate expanded syntax tree have the existing
depth/index/node limits. The final expanded request also has the shared
10,000-node budget; nested abbreviations cannot evade it by hiding duplication
behind compact source. Expansion may therefore reject a small source whose
expanded form exceeds bounds. The shared 50,000 proof-step limit also applies.
General congruence and dependent transport, type-directed composition and
Glue-directed composition and fresh ua construction remain open. Source elaboration correctness and
the semantic adequacy of the object specification remain separate proof
obligations from certificate checking.
