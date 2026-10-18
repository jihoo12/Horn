# Schematic certificates and proof generalization (research)

Status: research prototype on branch `research/schematic`. Nothing here is
part of the trusted kernel. `src/kernel.rs`, the parser, and
`agda/Soundness.agda` are unchanged; every ground instance mentioned below was accepted by the
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


## Mechanized soundness

[agda/Schematic.agda](../agda/Schematic.agda) proves the inference forms
sound, with `--safe --without-K --no-libraries` like `Soundness.agda`.
Unlike that model it is sorted: eigenvariables have sorts, and derivations
use only well-sorted ground instances of the rules, so a sort without ground
terms is represented faithfully.

- `Valid H J`: for every well-sorted ground substitution of the variables
  of H and J, if every hypothesis instance is derivable then so is the
  instance of J.
- `H ⊢ J` has one constructor per accepted form: `hyp`, `inst` (instances of
  hypothesis-free facts by well-sorted substitutions), `step` (a rule with
  well-sorted bindings, premises from earlier facts, and the premise variable
  condition), and `induct` (one case per constructor of X's sort, with
  distinct fresh case variables of the constructor's argument sorts, X
  occurring in J, and only induction hypotheses as hypotheses).
- `sound : H ⊢ J → Valid H J`, and so `soundness`: every well-sorted ground
  instance of a hypothesis-free accepted judgment is derivable.

The induction case is proved by structural induction on the well-sortedness
derivation of the ground term substituted for X. Two checked examples
accompany the proof. One builds `max L L L` by induction and obtains
`max 2 2 2` from `soundness`. The other shows the premise variable condition
is necessary: in a theory with an empty sort, `p X` is accepted, the step
`p X ⊢ q` fails the condition, and `q` is provably not derivable.

The module `Algorithm` then models the checking algorithm, as
`Soundness.agda` does for ground certificates. Steps are checked in order
and may reference only earlier ones; rule bindings are found by matching;
instance substitutions are sort-checked; the premise variable condition is
decided on variable lists; and induction cases are aligned with a list of
the sort's constructors, which must name every constructor.
`accepts-sound` proves that an accepted certificate makes every
well-sorted ground instance of every goal derivable. The `max` certificate
evaluates to accepted, and a circular induction and the empty-sort step
evaluate to rejected.

The model makes the same checks as `src/schematic.rs`. In particular it
does not check the sorts of bindings found by matching: given well-formed
rules (`RuleWF`, judgments well-sorted for the rule variables' sorts, which
the kernel's theory parser checks) and the invariant that every fact is
well-sorted, matching is proved to yield well-sorted bindings. The model
keeps hypotheses as judgments rather than step indices; every hypothesis in
Rust comes from a `hyp` step, so this loses nothing. Parsing, names, `def`
and hash-consing are not modelled, and no proof connects the Rust code to
the model.

### Checking Rust output with the Agda model

No proof connects the Rust code to the model, but a certificate the Rust
checker accepted can be checked by the model too.
`schematic-kernel --agda MODULE THEORY GOALS PROOF OUT.agda` writes an Agda
module with the theory as tables, the goals as explicit terms, and the
certificate as a stream of naturals (`Code`). Its last line,
`theorem = acceptsCode-sound goals code refl`, makes Agda decode the
certificate and run the modelled checker on it; the model is the algorithm
proved sound above, so this gives the soundness theorem for those goals
without trusting `src/schematic.rs`. The exporter and the decoder are
untrusted: whatever certificate decoding yields must still be accepted for
the goals the module states. Rule well-formedness and constructor
completeness are decided inside Agda too.

[agda/LevelsCertificate.agda](../agda/LevelsCertificate.agda) is the export
of the levels example; `nix flake check` checks it, and a test keeps it in
sync with the Rust output. Changing the goal in it makes Agda reject it
(`nothing != just tt`).

On kamo3's level-generalized certificates, with its 412-rule theory (the
first version of the model, before the changes below, in parentheses):

| Certificate | Steps | Agda module | Agda check |
| --- | ---: | ---: | ---: |
| constant-transport | 318 | 178 kB | 6.4 s (5 s) |
| transport | 588 | 212 kB | 7.5 s (7.6 s) |
| to-pathp | 1,564 | 341 kB | 12 s (20 s) |
| homotopy | 4,038 | 675 kB | 33 s (117 s) |
| contr-prop | 4,579 | 739 kB | 26 s (162 s) |
| ua-beta | 36,797 | 5.3 MB | 284 s, 12 GB |

The first version grew quadratically. Four changes made it linear:

- Facts are kept in a Braun tree, with builtin halving and parity, rather
  than a list extended at the end and searched by unary index.
- The rule step checks only what is not already implied: sorts of bindings
  of conclusion-only variables, and the variables of bindings of
  premise-only variables. The proof derives the rest.
- The certificate is a stream of naturals with no implicit arguments, so
  Agda elaborates it quickly.
- `refl` is passed straight to the soundness lemma; a separate
  `accepted` lemma made Agda run the checker twice.

About half of the remaining time is evaluation, much of it comparing
large terms structurally where Rust compares hash-consed indices. Memory
grows with the certificate: ua-beta needs 12 GB, so univalence (185,682
steps) does not fit in 30 GB. Hash-consing terms inside the model would
address both.

## What this does and does not establish

- The schematic checker is a prototype outside the trusted kernel. Its
  checking algorithm is modelled and proved sound in Agda (above), but no
  proof connects the Rust code to that model; individual certificates can
  be re-checked by the model instead. Instances at concrete levels are checked
  by the unchanged kernel and do not depend on either.
- A goal over `L` is a schema: it states every ground instance. It is not an
  internal universe-polymorphic term of the object theory.
- One eigenvariable per goal. Goals whose levels must vary independently
  (`Π A:U_i, B:U_j`) would need several, and then `max` facts relating them
  are not provable by induction on one.
- Induction is structural on the eigenvariable's sort, with one predicate at
  a time; the generalizer only proposes inductions for cut judgments.

## Next steps

1. Decide whether the kernel adopts schematic checking. Connecting either
   Agda model to the Rust code (by verifying the Rust, or by differential
   testing on a broad corpus) remains open for both kernels.
2. Hash-cons terms in the model, so that the large kamo3 certificates,
   univalence included, can be re-checked in Agda within memory.
3. Let kamo3 producers build at a symbolic level directly, instead of
   generalizing a level-0 proof afterwards.
4. Several eigenvariables, with lemmas such as `max i j k → max j i k`
   proved by induction.
5. Use the same mechanism for other admissible rules that kamo3 currently
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
