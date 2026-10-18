# Cubical scripts: certified evaluation through univalence

`horn cubical eval FILE.hcs` reads definitions, typing checks and
evaluations, elaborates them to the cubical core, and certifies them with
the engine moved from kamo3 (`cubical::engine`). Every form becomes a fixed
goal of one derivation. The derivation is encoded as an oracle and checked
by the unchanged ground kernel against the bundled theory. Values are
printed only after that check succeeds.

```text
(def not (pi b bool bool) (lam b bool (bif c bool bfalse btrue b)))
(def not-not (pi b bool (path bool (app not (app not b)) b))
  (lam b bool
    (bif c (path bool (app not (app not c)) c) (plam i btrue) (plam i bfalse) b)))
(def not-equiv (equiv bool bool)
  (pair not (app iso-equiv bool bool not not not-not not-not)))
(def not-path (path (u 0) bool bool) (app ua bool bool not-equiv))
(eval along-ua (transport i (papp not-path i) btrue))
```

```sh
cargo run --release --locked --offline --bin horn -- cubical eval examples/cubical/script/bool.hcs
```

```text
not-true = bfalse : bool
along-ua = bfalse : bool
ACCEPT (cubical script): 6 goals, 237149 proof steps, 54574 oracle bytes
```

This takes about 8 seconds and 0.25 GB. `--emit NEW_DIR` writes `theory.horn`, `goals` and
`proof.oracle` for independent checking with `oracle-kernel`.

Natural numbers ([nat.hcs](../examples/cubical/script/nat.hcs)) support
programs by recursion and proofs by induction, in 0.1 s:

```text
(def add (pi m nat (pi n nat nat))
  (lam m nat (lam n nat (natrec k nat m (lam k nat (lam r nat (suc r))) n))))
(eval two-plus-three (app add 2 3))                        ; 5 : nat
(def zero-add (pi n nat (path nat (app add 0 n) n))
  (lam n nat
    (natrec k (path nat (app add 0 k) k)
      (plam i 0)
      (lam k nat (lam p (path nat (app add 0 k) k) (plam i (suc (papp p i)))))
      n)))
```

Functions move along ua too ([function.hcs](../examples/cubical/script/function.hcs),
about 22 s): transporting `not` along the line `i ↦ (ua not i → ua not i)`
gives a function that maps `btrue` to `bfalse` and `bfalse` to `btrue`, as
conjugating `not` by `not` should. This goes through composition in Pi types,
then Glue, then bool.

## Declared data types

`(data NAME (CTOR ARG-TYPE...) ...)` declares a closed data type
([data.hcs](../examples/cubical/script/data.hcs), about 9 s):

```text
(data color (red) (green) (blue))
(def next (pi c color color) (lam c color (elim color k color (green blue red) c)))
(def rotate (equiv color color) (pair next (app iso-equiv color color next prev next-prev prev-next)))
(eval along-ua (transport i (papp (app ua color color rotate) i) red))   ; green : color
(data tree (leaf) (node tree nat tree))
```

A declaration generates its rules as text: formation, constructors and
their congruence, a dependent eliminator whose method types are spelled out
with certified shifts and substitutions, one computation rule per
constructor, congruence, scope/shift/substitution rules, and composition.
They are appended to the bundled theory, written by `--emit` to
`theory.horn`, and the oracle is checked against that combined theory; a
reader sees exactly which rules a script introduced. Nothing about the
declaration is built into the engine or the kernel.

Type parameters are declared as `(data (list A) (nil) (cons A (list A)))`
([list.hcs](../examples/cubical/script/list.hcs), about 8 s). Constructors and
eliminators take the parameters first: `(cons bool btrue (nil bool))`,
`(elim list (bool) k P (METHODS...) x)`. Moving a list along `ua not` runs
`not` on every element:

```text
(eval moved (transport i (list (papp not-path i)) (cons bool btrue (cons bool btrue (nil bool)))))
; moved = (cons bool bfalse (cons bool bfalse (nil bool))) : (list bool)
```

Fields may be `bool`, `nat`, a parameter, earlier closed data types, or the
type itself at its own parameters. Without function or universe fields,
strict positivity is immediate. Composition rules depend on parameters:

- A closed type has only discrete fields, so it is discrete (a constant
  presheaf in the cubical-set model) and composition returns its base.
- A parameterized type gets one transport rule per constructor, for the
  empty face: `transp (T A) (c a…) = c (transp A a)…`, as in the standard
  models of inductive families. Compositions with other faces have no rule
  and stay unevaluated; the transports that ua needs all use the empty face.

The type, its constructors and its eliminator also get congruence rules,
including conversion of parameters. Indices, function-typed fields and
higher constructors are not supported.

## What this language is for

It is not meant to become Lean 4. Its distinguishing commitments are:

- The trusted checker is a generic Horn derivation checker; the type theory
  is a rule file, and every declaration's rules are explicit data.
- Univalence computes: transport along an equivalence runs as a program
  (`along-ua` above), on booleans, functions and declared data.
- Every result is a portable certificate (tens of kilobytes) that anyone can
  re-check against the stated theory and goals, independently of the
  elaborator and the engine that produced it.

## Forms

- `(data NAME (CTOR FIELD-TYPE...) ...)` or `(data (NAME PARAM...) ...)`: a data
  type (above). Constructors
  apply like functions; `(elim NAME k P (METHODS...) x)` eliminates `x` into
  the motive `P` over `k : NAME`, with one method per constructor taking its
  arguments and then one induction hypothesis per recursive argument.
- `(def NAME TYPE TERM)`: a closed, transparent definition. Its typing is a goal.
- `(check NAME TERM TYPE)`: a typing goal.
- `(eval NAME TERM [TYPE])`: weak-head evaluation, continued under `suc` for
  natural numbers so a closed number reaches a numeral. The goal is
  `TERM ≡ VALUE : TYPE`, with every step an explicit derivation. Without a
  type, the inferred type is reported in weak-head normal form.
- `(equal NAME LEFT RIGHT TYPE)`: an equation found by the engine's search.

Terms use named binders: `(lam x A body)`, `(pi x A B)`, `(sigma x A B)`,
`(app f a ...)`, `(pair a b)`, `(fst p)`, `(snd p)`, `(plam i body)`,
`(path i A l r)` or `(path A l r)`, `(papp p r)`, `(bif c P t f b)` with
motive `P` over `c : bool`, `(ann t A)`, `(u N)`, `(equiv A B)` and
`(transport i A x)`, `(suc n)`, `(natrec k P z s n)` with motive `P` over
`k : nat` and step `s : Π k. P k → P (suc k)`, and numerals. Intervals are `i0`, `i1`, names, `neg`, `meet` and
`join`. Constants are `bool btrue bfalse nat zero`.

The prelude has two closed library terms from kamo3: `ua` and `iso-equiv`.
Their typings are checked in each run like a definition. Neither is an
axiom, and neither adds a rule.

## Trust

The elaborator, the engine's search and the oracle encoder are untrusted.
Acceptance means the fixed goals are derivable from the bundled rules,
including [bool.horn](../theories/cubical/bool.horn). The rules' adequacy for
cubical type theory is still a separate obligation; see [CUBICAL.md](CUBICAL.md).

## Limits

Evaluation is weak-head and bounded by 100,000 steps. Universe levels are
fixed at 0 for the prelude. Data types are bool, nat and declared types with parameters but no indices;
there are no implicit arguments and no modules. This format and the `.hcu` core files
and `.hn` programs are still separate frontends.
