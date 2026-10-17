# Schematic certificates and proof generalization (research)

Status: research prototype on branch `research/schematic`. Nothing here is
part of the trusted kernel. `src/kernel.rs`, the parser, and the Agda proof
are unchanged; every ground instance mentioned below was accepted by the
unchanged `kernel`.

## Question

Ground Horn certificates can only state ground facts. kamo3 proves
univalence at U₀, and its plan lists higher universe levels as open: each
level needs its own certificate, and no certificate can say "for every
level". Can a checker that stays generic, with no notion of universes, check
statements over every level, and can such certificates come from the proofs
that already exist?

## First hypothesis, refuted: lemma reuse

The first idea was derived rules: prove a lemma once with schema variables,
then instantiate it, so that certificates shrink. `horn-generalize` measures
this. The *skeleton* of a step is its rule plus its premises' skeletons,
ignoring terms. Steps with one skeleton are instances of one derived rule,
whose most general judgment is the skeleton's rules composed by unification.

| Certificate | Steps | Skeletons | Ratio | Substitution entries |
| --- | ---: | ---: | ---: | ---: |
| ua-beta | 36,791 | 24,686 | 0.67 | 168,814 |
| compute | 72,717 | 33,317 | 0.46 | 310,496 |
| deep-univalence | 185,673 | 117,403 | 0.63 | 1,473,375 |
| equiv-ext | 63,496 | 13,427 | 0.21 | 216,789 |

Sharing every repeated sub-derivation saves at most half the steps (five
times for equiv-ext). The most general judgments are as large as the ground
terms, and each reference needs a substitution four to eight times the
number of steps. A schematic certificate built this way is not smaller than
a compact one, and oracle certificates already solve size. These proofs
follow the structure of their terms; they do not repeat.

## Finding: the proofs are level-generic except for level arithmetic

The same analysis gives explanation-based generalization: the most general
judgment of a goal's skeleton is what the same proof establishes when the
goal's constants are not fixed. At first nothing generalized. Level
arithmetic is the reason. `max` is defined by recursion on numerals:

```text
(rule max.z () (max z ?n ?n))
(rule max.sz () (max (s ?n) z (s ?n)))
(rule max.ss ((max ?m ?n ?k)) (max (s ?m) (s ?n) (s ?k)))
```

`max l l l` holds for every `l` but is not derivable for a variable `l`; it
is *admissible*, by induction on `l`. Excluding `max` from generalization
(a *cut* predicate) shows the rest: every universe level in the ua-beta and
univalence proofs becomes one variable, and the only remaining obligations
are `max` facts about it.

## Schematic certificates

[`src/schematic.rs`](../src/schematic.rs) checks Horn certificates over open
judgments. It adds four forms; ground certificates keep their verdict.

```text
(var NAME SORT)                     eigenvariable, in goals or certificate
(hyp N JUDGMENT)                    step N assumes JUDGMENT
(induct N X JUDGMENT (CASE...))     JUDGMENT for every X
CASE = (INDEX Y...)                 one per constructor of X's sort
REF  = INDEX | (INDEX (VAR TERM)...)
```

A step with judgment J and hypotheses H is valid when every ground instance
of J follows from the theory whenever the same instance of H does, over the
variables of J and H. The checker keeps that invariant:

- A rule step's premise instances and bindings may use only variables of its
  conclusion or hypotheses. Otherwise a variable of an empty sort could stand
  for a term that does not exist (test
  `a_free_premise_variable_of_an_empty_sort_is_rejected`).
- Only hypothesis-free steps are instantiated by a substitution.
- `induct` on X of sort S requires X to occur in J and one case per
  constructor c of S, proving J[X := c(Y...)] for distinct fresh Y. Its
  hypotheses must be `hyp` steps J[X := Y] for the Y of sort S. Ground terms
  of S are finite constructor trees, so induction on them gives every
  instance of J. Without the occurrence condition, a sort whose constructors
  are all recursive has no ground terms, and each case could be its own
  hypothesis; this hole was found in review and has a test
  (`induction_variable_must_occur_in_the_judgment`).
- Results must be hypothesis-free and equal their goals exactly. A goal with
  variables states all its ground instances.

`schematic-kernel THEORY GOALS PROOF VAR=TERM OUT_GOALS OUT_PROOF` also
unfolds a schematic certificate at a ground instance, expanding inductions
along the term, into an ordinary certificate for the unchanged `kernel`.
That gives a check of any instance that does not trust the prototype.

## Generalizing existing proofs

`horn-generalize THEORY GOALS PROOF max:2 u:0 OUT_GOALS OUT_PROOF` turns a
ground certificate into a schematic one. `max:2` cuts `max` and declares its
third argument a function of the others. `u:0` names the positions to
abstract: the argument of `u`.

1. The skeleton analysis gives each goal's most general statement. Its
   variables at `u:0` become one rigid eigenvariable `L`.
2. For each goal separately, the steps it needs become one unification
   problem. Each use of a cut judgment gets fresh variables, since one ground
   `max z z z` may stand for differently generalized facts.
3. An open `max` output takes the first candidate that can be derived: one
   of the inputs, or the ground proof's value. Cut judgments are derived by
   backward chaining with the theory's own rules, and otherwise by induction
   on `L`. Everything still open takes the ground proof's value.
4. A goal whose proof pins `L`, or whose cut judgments fail, is written with
   its ground statement instead.

The generalizer is untrusted; `schematic-kernel` decides.

## Results on kamo3

All 24 ordinary deep certificates, 84 goals. For each: generalize, check the
schematic certificate, unfold at `L := z` and compare with the original
goals, unfold at `L := 1` and check with the unchanged ground `kernel`.

| Certificate | Steps | Goals over L | Inductions | Schematic | L := z | L := 1 |
| --- | ---: | ---: | ---: | --- | --- | --- |
| deep | 688 | 0/9 | 0 | accept | same | accept |
| equiv | 530 | 1/8 | 1 | accept | same | accept |
| glue | 1,622 | 0/10 | 0 | accept | same | accept |
| identity | 1,345 | 2/2 | 1 | accept | same | accept |
| ua | 11,120 | 3/3 | 2 | accept | same | accept |
| ua-graph | 17,707 | 4/4 | 2 | accept | same | accept |
| transport | 588 | 3/3 | 2 | accept | same | accept |
| ua-beta | 36,797 | 3/3 | 2 | accept | same | accept |
| homotopy | 4,038 | 2/2 | 2 | accept | same | accept |
| transport-equiv | 39,921 | 3/3 | 2 | accept | same | accept |
| glue-fiber | 76,788 | 3/3 | 2 | accept | same | accept |
| contr-prop | 4,579 | 1/1 | 1 | accept | same | accept |
| isequiv-prop | 25,300 | 1/1 | 2 | accept | same | accept |
| to-pathp | 1,564 | 3/3 | 2 | accept | same | accept |
| ua-unglue-center | 100,347 | 1/1 | 1 | accept | same | accept |
| equiv-ext | 63,502 | 1/1 | 2 | accept | same | accept |
| canonical-map | 35,755 | 2/2 | 2 | accept | same | accept |
| compute | 102,361 | 4/12 | 3 | accept | same | accept |
| constant-transport | 318 | 6/6 | 1 | accept | see below | accept |
| deep-univalence | 185,682 | 2/2 | 3 | accept | same | accept |
| iso-equiv | 46,421 | 1/1 | 2 | accept | same | accept |
| glue-comp | 41,958 | 2/2 | 1 | accept | same | accept |
| canonical-ua | 54,401 | 1/1 | 3 | accept | same | accept |
| ua-transport | 18,852 | 1/1 | 1 | accept | same | accept |

50 of 84 goals hold for every level. Every goal that stays ground mentions
`nat`, whose rule fixes it at U₀ (there is no cumulativity), or has no
universe to abstract. constant-transport has separate level-0 and level-1
goals; both generalize to the same statement, whose instance at `L := z`
reproduces the three level-0 goals and at `L := 1` the three level-1 goals.

In particular `closed-deep-univalence`,

```text
Π A B : U_L. Equiv (Path U_L A B) (Equiv A B)
```

is accepted for a variable `L`: all 136 occurrences of `(u z)` in the goal
become `(u L)` and the four `(u (s z))` become `(u (s L))`. The proof needed
three inductions, each a `max` fact such as `max L L L` or `max (s L) L (s L)`.
The schematic certificate has 185,682 steps and checks in under half a second.

The three large certificates, regenerated byte-for-byte from kamo3 (digests
match `examples/*.proof.sha256`), give the same result:

| Certificate | Size | Steps | Goals over L | Inductions | Schematic | L := z | L := 1 |
| --- | ---: | ---: | ---: | ---: | --- | --- | --- |
| ua-unglue | 4.07 GB | 1,128,758 | 1/1 | 2 | accept | same | accept |
| constant-equiv | 762 MB | 530,403 | 1/1 | 2 | accept | same | accept |
| ua-eta | 1.67 GB | 1,072,045 | 1/1 | 3 | accept | same | accept |

For ua-unglue the schematic certificate is 92.7 MB; generalizing took 7.6
minutes, mostly reading the ordinary certificate. Unfolding it at `L := 1`
took 9.9 s and the ground kernel checked the result in 1.2 s.


## What this does and does not establish

- The schematic checker is a prototype. Its soundness argument is above;
  it is not mechanized, and the Agda model covers only ground certificates.
  Instances at concrete levels are checked by the unchanged kernel and do not
  depend on it.
- A goal over `L` is a schema: it states every ground instance. It is not an
  internal universe-polymorphic term of the object theory.
- One eigenvariable per goal. Goals whose levels must vary independently
  (`Π A:U_i, B:U_j`) would need several, and then `max` facts relating them
  are not provable by induction on one.
- Induction is structural on the eigenvariable's sort, with one predicate at
  a time; the generalizer only proposes inductions for cut judgments.

## Next steps

1. Mechanize the schematic invariant in Agda next to `Soundness.agda`, then
   decide whether the kernel adopts schematic checking.
2. Let kamo3 producers build at a symbolic level directly, instead of
   generalizing a level-0 proof afterwards.
3. Several eigenvariables, with lemmas such as `max i j k → max j i k`
   proved by induction.
4. Use the same mechanism for other admissible rules that kamo3 currently
   re-derives on ground numerals (de Bruijn index arithmetic).

## Reproduce

```sh
cargo run --release --bin horn-generalize -- \
  examples/levels.horn examples/levels.goals examples/levels.proof \
  max:2 u:0 /tmp/levels.L.goals /tmp/levels.L.proof
cargo run --release --bin schematic-kernel -- \
  examples/levels.horn /tmp/levels.L.goals /tmp/levels.L.proof
cargo run --release --bin schematic-kernel -- \
  examples/levels.horn /tmp/levels.L.goals /tmp/levels.L.proof \
  'L=(s (s z))' /tmp/levels.2.goals /tmp/levels.2.proof
cargo run --release --bin kernel -- \
  examples/levels.horn /tmp/levels.2.goals /tmp/levels.2.proof
```

The kamo3 results need an authorized kamo3 checkout and its concatenated deep
theory, as in `scripts/check-kamo3.sh`.
