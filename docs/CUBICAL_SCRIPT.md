# Cubical scripts: certified evaluation through univalence

`horn cubical eval FILE.hcs` reads definitions, typing checks and
evaluations, elaborates them to the cubical core, and certifies them with
the engine moved from kamo3 (`cubical::engine`). Every form becomes a fixed
goal of one derivation. The derivation streams from the engine to the
unchanged ground kernel, which checks it against the bundled theory. Values
are printed only after that check succeeds. With `--emit`, the derivation is
instead encoded as an oracle, and the kernel checks the decoded oracle, so
the certificate written out is exactly what was accepted. Both paths check
the same steps against the same goals. The direct path skips encoding and
decoding, which took about half the time of a run.

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
ACCEPT (cubical script): 6 goals, 83756 proof steps, 15467 oracle bytes
```

This takes about 0.6 seconds and 0.1 GB. `--emit NEW_DIR` writes `theory.horn`, `goals` and
`proof.oracle` for independent checking with `oracle-kernel`.

## Holes

Write `?` or `(? NAME)` for a part of a term you have not written yet. The
form is not certified; instead every hole is reported with what it must be:
the variables and dimensions in scope by their names, the face it lives
under, the type it must have, and, for the body of a path abstraction, the
values it must take at the ends:

```text
(def zero-add (pi n nat (path nat (app add 0 n) n))
  (lam n nat
    (natrec k (path nat (app add 0 k) k)
      (plam i ?)
      (lam k nat (lam p (path nat (app add 0 k) k) (? step)))
      n)))
```

```text
error: def zero-add: 2 goals to fill

?1
  n : nat
  i : I
  ⊢ nat
  where i = 0 must give (app add 0 0)
        i = 1 must give 0

?step
  n : nat
  k : nat
  p : (path nat (app add 0 k) k)
  ⊢ (path nat (app add 0 (suc k)) (suc k))
```

Checking continues past a hole (it is taken to fit, with a placeholder step
that no theory accepts), so all holes of a form are shown at once. Terms
print as they are written: definitions by name, numerals as numbers,
declared data by their declared names, faces simplified, and a variable
shadowed by a later one of the same name as `x✝`. A hole whose type the
checker cannot know there (the head of an application) says so, and so does
one whose required type is not a type. Equations between terms with holes,
as in `(equal e ? 0 nat)`, are listed after the goals (`?1 = 0 : nat`),
since a hole's type alone does not say what it must equal. Holes are
numbered in the order they are written; a hole anywhere in a form, even in
a position the checker does not use, keeps the form from being certified.
In a `def-poly`, goals show the level variable (`⊢ (u L)`).

## When a proof is wrong

A form that does not check says where, in the same names: a path that does
not end where it must, a term whose type is not the one required, or a
function, pair or path given where the type has no such elements. Each side
is also shown evaluated when that differs. Forgetting `suc` in the step of
`zero-add` above gives:

```text
error: def zero-add: the path does not end where it must, at i = 0

  n : nat
  k : nat
  p : (path nat (app add 0 k) k)

  it is (papp p 0), which computes to (natrec x nat 0 (lam x (lam y (suc y))) k)
  but must be (app add 0 (suc k)), which computes to (suc (natrec x nat 0 (lam x (lam y (suc y))) k))
```

The checker's search may fail in several places before giving up; the
report is the last mismatch on the path that failed, not one it recovered
from.

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
about 1 s): transporting `not` along the line `i ↦ (ua not i → ua not i)`
gives a function that maps `btrue` to `bfalse` and `bfalse` to `btrue`, as
conjugating `not` by `not` should. This goes through composition in Pi types,
then Glue, then bool.

## Declared data types

`(data NAME (CTOR ARG-TYPE...) ...)` declares a closed data type
([data.hcs](../examples/cubical/script/data.hcs), about 0.6 s):

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
([list.hcs](../examples/cubical/script/list.hcs), about 0.6 s). Constructor
terms do not carry the parameters, `(cons btrue nil)`: the engine reads them
off a field at a parameter or, as for an unannotated lambda, off the expected
type; a lone `nil` needs one. The eliminator takes them explicitly,
`(elim list (bool) k P (METHODS...) x)`. Moving a list along `ua not` runs
`not` on every element:

```text
(eval moved (transport i (list (papp not-path i)) (cons btrue (cons btrue nil))))
; moved = (cons bfalse (cons bfalse nil)) : (list bool)
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

The type (in its parameters), its constructors and its eliminator also get
congruence rules. Indices and function-typed fields are not supported;
path constructors are (below).

## Programs move along equivalences

[binary.hcs](../examples/cubical/script/binary.hcs) (about 1.3 s) declares
binary numbers in bijective base 2, `(data bin (bz) (b1 bin) (b2 bin))` for
0, 2b+1 and 2b+2, proves `nat ≃ bin` with conversions in both directions and
their inverse laws (by induction, with path composition defined by
transport), and turns it into a path `nat-is-bin : Path U0 nat bin` with
`ua`. Addition is written once, on unary `nat`; binary addition is obtained
by transport and is never written:

```text
(def add-bin (pi a bin (pi b bin bin))
  (transport i (pi a (papp nat-is-bin i) (pi b (papp nat-is-bin i) (papp nat-is-bin i))) add))
(eval three-plus-two (app add-bin (b1 (b1 bz)) (b2 bz)))
; three-plus-two = (b1 (b2 bz)) : bin                 that is, 3 + 2 = 5
```

Evaluation runs the transport: composition in Pi types transports the
arguments back along the Glue line to `nat` (through `to-nat`), adds, and
transports the sum forward (through `from-nat`), all as checked steps.

## The circle and its winding number

[circle.horn](../theories/cubical/circle.horn) adds the circle, a higher
inductive type: `s1`, `base`, a path constructor `(loop r)` with
`loop i0 = loop i1 = base`, and the recursor `(s1rec A b l x)` for `b : A`
and `l : Path A b b`, which computes on `base` and on `(loop r)`.
[circle.hcs](../examples/cubical/script/circle.hcs) declares the
integers, proves the successor an equivalence, and defines the universal
cover `helix x = s1rec U0 int (ua sucEquiv) x`. Transporting `0` along
`helix` over a loop counts its windings:

```text
(def winding (pi p (path s1 base base) int)
  (lam p (path s1 base base) (transport i (app helix (papp p i)) (pos 0))))
; winding loop = (pos 1), winding refl = (pos 0), winding loop⁻¹ = (negsuc 0)
```

### Composite loops

The circle is not discrete, so composition in `s1` cannot return its base.
Following Coquand, Huber and Mörtberg (2018), a composition in the constant
family `s1` is instead a *formal* point: the homogeneous composition
constructor. Horn needs no new constructor for it, since `(comp s1 φ u u0)`
is already well typed by the composition rules and nothing reduces it; one
rule, `req.s1rec-comp`, lets the recursor commute with it:

```text
s1rec A b l (hcomp^j [φ ↦ u] u0) ≡ hcomp^j_A [φ ↦ s1rec A b l u] (s1rec A b l u0)
```

Compositions are written `(hcomp j A ((FACE TERM) ...) BASE)`, or
`(comp j A ...)` when the type depends on `j`, with faces `(= i 0)`,
`(= i 1)`, `(and F G)`, `(or F G)`. Path composition is then a definition,
and the winding number of `loop · loop` computes (about 2 s, 0.3 GB):

```text
(def compose (pi p (path s1 base base) (pi q (path s1 base base) (path s1 base base)))
  (lam p (path s1 base base) (lam q (path s1 base base)
    (plam i (hcomp j s1 (((= i 0) base) ((= i 1) (papp q j))) (papp p i))))))
(eval loop-twice (app winding (app compose (plam i (loop i)) (plam i (loop i)))))
; loop-twice = (pos 2) : int
```

`helix` sends the composite loop to a composition in the universe,
`hcomp^j_U [i=0 ↦ int, i=1 ↦ ua suc j] (ua suc i)`, which is a Glue type
(`req.comp-universe`); transporting `0` through it runs Glue composition,
which takes the center of a fiber of the universe's line equivalence.

Two changes make that run in a minute instead of not finishing:

- **The line equivalence is direct.** `canonical-map`, the equivalence that
  universe composition glues along, used to transport the identity
  equivalence and its contractibility evidence along the line, so each
  fiber center cost a composition in a Π of Σ of path types over Glue
  types. It is now the transport `f` made an equivalence by `iso-equiv`
  with the transport `g` back and two filling squares
  (`canonical_code_frontend`), so a fiber center is `(g y, s y)`: one
  transport back along the line. It is still a fixed program whose typing
  is checked at every use; any equivalence is a valid choice for the
  universe's composition structure.
- **Closed terms are typed once.** `rhas.closed` and `req.closed`
  ([closed.horn](../theories/cubical/closed.horn)) weaken a typing or
  equation of a closed term in the empty context to any well-formed
  restricted context, with its dimensions and face; the engine uses them
  for annotated closed terms such as `ua`, `iso-equiv` and the line
  equivalence, which were otherwise re-checked at every dimension depth and
  face they were used under, and for every other closed term that types in
  the empty context (`int`, closed Π and Σ types, ...), which were
  otherwise lifted into each context one binder at a time.

## Declared higher inductive types

A constructor whose last item is `(path LEFT RIGHT)` is a path constructor
([hit.hcs](../examples/cubical/script/hit.hcs), about 0.8 s). It may have
fields (bool, nat, earlier closed data types, the type itself), and its
terms take an interval after them. A field may be named, `(x TYPE)`. Each
endpoint is one of the constructor's fields of the type itself, or a point
constructor applied to endpoints, where a position of a closed type takes a
field of that type or a closed term:

```text
(data circle (pt) (lp (path pt pt)))
(data susp (north) (south) (merid bool (path north south)))
(eval merid-true (app wind (plam i (app to-circle (merid btrue i)))))   ; (pos 1) : int
(data trunc (inc nat) (squash (x trunc) (y trunc) (path x y)))
(data glued (left nat) (right nat) (seg (n nat) (path (left n) (right n))))
```

For a path constructor the declaration also generates:

- typing with an interval premise, and scope/shift/substitution rules that
  map the interval by dimension operations only;
- its boundary, `(c a… r) ≡ LEFT` when `r = 0` holds under the face, and
  `≡ RIGHT` when `r = 1`, and congruence in the fields and the interval;
- an eliminator method of type `Π a…. Π h…. PathP (i. P (c a… i)) e₀ e₁`,
  with an induction hypothesis `h : P a` for every recursive field `a`, where
  `e₀`, `e₁` are the eliminator's values on the endpoints spelled out with
  the methods and hypotheses (stating them with the eliminator would make
  its typing rule circular), and the computation
  `elim … (c a… r) ≡ (m a… (elim … a)…) @ r`;
- instead of a composition rule, the eliminator on a formal composition
  (CHM 2018), `req.E.hcomp`:

```text
elim P m… (hcomp^j_T [φ ↦ u] u0)
  ≡ comp^j (P (hfill^j [φ ↦ u] u0)) [φ ↦ elim P m… u] (elim P m… u0)
```

with the filler given by `filldef`, so the motive may depend on the point.
For a type with parameters the composition must be homogeneous: its family
is the type at the parameters weakened by the composition's dimension.
A type with a path constructor is not discrete, so it gets no rule that
returns a composition's base. With the declared circle, `wind (lp · lp)`
also computes to `(pos 2)` (about 60 s), through this dependent rule
rather than the built-in `s1rec` one.

A higher inductive type may have parameters
([hit-params.hcs](../examples/cubical/script/hit-params.hcs), about 0.5 s),
and its fields may be at a parameter:

```text
(data (susp A) (north) (south) (merid A (path north south)))
(data (ptrunc A) (inc A) (squash (x (ptrunc A)) (y (ptrunc A)) (path x y)))
(equal flip-merid
  (plam i (transport j (susp (papp flip j)) (merid btrue i)))   ; flip = ua not
  (plam i (merid bfalse i))
  (path (susp bool) north south))
```

Transport along the empty face moves a path constructor's fields and keeps
its interval, `transp (T A) (c a… r) = c (transp A a)… r`. Endpoints are
built from constructors and fields, and transport commutes with those
strictly, so this agrees with the boundary at `r = 0` and `r = 1`; no
correcting composition is needed (CHM 2018 need one for general endpoints).
Transport of a formal composition has no rule yet and stays unevaluated.
Endpoints are point terms; higher-dimensional constructors (a torus's
square) are not supported.

## Implicit arguments

A def's type may start with implicit binders, `(pi {A} TYPE ...)`
([implicit.hcs](../examples/cubical/script/implicit.hcs), about 0.1 s). Their
names are in scope in the body, which the elaborator puts under one lambda
for each. An application `(app f a ...)` fills them in. `(@ f)` is `f`
taking them explicitly:

```text
(def sym (pi {A} (u 0) (pi {x} A (pi {y} A (pi p (path A x y) (path A y x)))))
  (lam p (path A x y) (plam i (papp p (neg i)))))
(check back (app sym (app refl 3)) (path nat 3 3))
(check given (app (@ sym) nat 1 1 (app refl 1)) (path nat 1 1))
```

To fill them in, the elaborator infers each explicit argument's type with the
engine, in the context of the binders around it. It then matches that type
against the parameter's domain, computing the type to weak-head normal form
if the shapes differ. This step is not trusted. The application is written
out with the arguments it found and then checked like any other term, so a
wrong guess is reported as a type mismatch. An argument whose type cannot
be inferred, such as an unannotated lambda, contributes nothing. If no
argument determines an implicit argument, elaboration stops and asks for
`(@ f)`. Implicit binders appear only at the start of a def's type, and a
bare reference to such a def is an error.

## Categories

[category.hcs](../examples/cubical/script/category.hcs) (about 0.5 s) defines
wild precategories as a nested Σ: objects in `U1`, morphisms in `U0`, and
the unit and associativity laws as paths. It then defines projections, the
category of types and functions, whose laws hold by `refl`, and the
opposite of any category.

Two kinds of engine support make this work:

- Types that only *compute* to a type former, such as `(app Hom A B)` for a
  `Hom` that returns a pi, are brought to weak-head normal form where a
  former is needed: η and congruence of introduction forms, application,
  projection and path-application congruence, β through an annotation, and
  a head step's type.
- A pair's component appears in the next component's type as a bare
  introduction form under that type's binders. It gets the type it was
  checked at, moved under those binders; the candidate is used only if
  shifting it back gives the term exactly, and it is checked again.

Definitions are constants, so terms stay the size they are written at, and
β through a definition's annotated body derives the typing of an
introduction-form reduct by subject reduction instead of checking the body
again. `Hom (op C) x y ≡ Hom C y x` and `Ob (op (op C)) ≡ Ob C` check
(about 0.5 s together). `Hom (op (op C)) x y ≡ Hom C x y` does not yet
finish: proving it under the laws' binders weakens typings one binder at a
time (`rhas.shift`), and those steps multiply.

## Universe levels

`ua` and `iso-equiv` are the prelude at level 0; `(ua-at L)` and
`(iso-equiv-at M N)` are the same closed terms at other levels, checked where
they are used. [levels.hcs](../examples/cubical/script/levels.hcs) (about 0.5 s)
builds `swap` on pairs of types, which live in `U1`, turns it into a path with
`(ua-at 1)`, and transports a function out of pairs of types along it.

Transporting a pair of types itself type-checks, but its components do not
reduce to `nat` and `bool`: they stay as Glue types with an empty face over
them. Transport along a constant line of types is not the identity without
regularity, which the CCHM model lacks. An equation `Glue A [ff ↦ …] ≡ A`
would force composition in that Glue type to agree with composition in `A`,
which reintroduces regularity, so the theory does not have it. Results
reach canonical form when they are data (booleans, numbers, declared types).

## Level variables

`(def-poly NAME (L) TYPE TERM)` states a definition for every universe level
`L` ([poly.hcs](../examples/cubical/script/poly.hcs), about 5 s, most of it
univalence). Levels are numerals, a level variable, or `(s LEVEL)`;
`(ua-at LEVEL)`, `(iso-equiv-at LEVEL)` and `(univalence-at LEVEL)` accept
level variables. `(at NAME LEVEL)` uses a definition at a level, including
the enclosing definition's own `L`.

```text
(def-poly univalence (L)
  (pi A (u L) (pi B (u L) (equiv (path (u L) A B) (equiv A B))))
  (univalence-at L))
; ACCEPT (schematic univalence): every level L, 198400 steps, 3 inductions
```

The ground kernel cannot state "for every L", so a polymorphic definition is
certified in three steps, reusing the research tools on schematic
certificates ([SCHEMATIC.md](SCHEMATIC.md)):

1. The engine proves the definition at level 0, as an ordinary certificate.
2. `generalize` abstracts the universe levels of that proof into one
   eigenvariable `L`, proving the `max` facts it needs by induction.
3. `schematic::check` accepts the result, and the script requires its goal
   to be exactly the stated judgment with `L` for the level variable. A
   proof that pins the level (for example `bool : U_L`) is rejected.

The level-0 instance also enters the script's ordinary certificate. `--emit`
writes `NAME.schematic.goals` and `NAME.schematic.proof`; `schematic-kernel
... L=(s z) OUT_GOALS OUT_PROOF` unfolds any instance into a ground
certificate for the unchanged kernel, which the tests do for univalence at
`L := 1`. The schematic checker is a research prototype modelled and proved
sound in [agda/Schematic.agda](../agda/Schematic.agda); it is not part of the
ground kernel.

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
  type (above); a constructor `(CTOR FIELD-TYPE... (path LEFT RIGHT))` is a
  path constructor, applied as `(CTOR a... r)`. Constructors
  apply like functions; `(elim NAME k P (METHODS...) x)` eliminates `x` into
  the motive `P` over `k : NAME`, with one method per constructor taking its
  arguments and then one induction hypothesis per recursive argument.
- `(def NAME TYPE TERM)`: a closed, transparent definition. Its typing is a goal.
  Later forms mention it as the constant `def/NAME`, which the engine
  unfolds (δ) only where computation needs the body; see [TRUST.md](TRUST.md)
  for its generated rules.
  `TYPE` may start with implicit binders `(pi {A} ...)` (above).
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
`(transport i A x)`, `(hcomp j A ((FACE TERM) ...) BASE)`,
`(comp j A ((FACE TERM) ...) BASE)`, `(suc n)`, `(natrec k P z s n)` with motive `P` over
`k : nat` and step `s : Π k. P k → P (suc k)`, and numerals. Intervals are `i0`, `i1`, names, `neg`, `meet` and
`join`. Constants are `bool btrue bfalse nat zero`.

The prelude has two closed library terms from kamo3: `ua` and `iso-equiv`.
Their typings are checked in each run like a definition. Neither is an
axiom, and neither adds a rule.

## Trust

The elaborator, the engine's search and the oracle encoder are untrusted.
Scripts are checked against the core theory (403 rules: the bundled theory
without its unrestricted judgment layer and one subsumed rule; see
[TRUST.md](TRUST.md)) plus the rules of their data declarations and
definitions. Acceptance
means the fixed goals are derivable from those rules,
including [bool.horn](../theories/cubical/bool.horn). The rules' adequacy for
cubical type theory is still a separate obligation; see [CUBICAL.md](CUBICAL.md).

## Limits

Evaluation is weak-head, continued under constructors and pairs, and bounded
by 100,000 steps. Each polymorphic definition has one level variable, and
declared data types live in `U0`. Data types are bool, nat and declared types with parameters but no indices;
implicit arguments are inferred only from explicit arguments, not from the
expected type, and there are no modules. This format and the `.hcu` core files
and `.hn` programs are still separate frontends.
