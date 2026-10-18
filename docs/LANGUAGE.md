# The Horn surface language (prototype)

`horn FILE.hn` reads a small language in the style of Lean: declare sorts,
constructors, predicates and rules, define functions by pattern matching,
evaluate, and prove theorems. Nothing in the implementation
([src/lang.rs](../src/lang.rs)) is trusted. Every answer and every theorem
becomes a step of one schematic certificate for the elaborated theory, and
the run fails unless the schematic checker accepts that certificate. The
certificate can also be exported for the proved Agda model to re-check.

```text
sort Nat
ctor zero : Nat
ctor succ : Nat → Nat

def add : Nat → Nat → Nat
| zero,   n => n
| succ m, n => succ (add m n)

pred le : Nat → Nat → Prop
rule le.zero : le zero n
rule le.succ : le m n → le (succ m) (succ n)

pred lt : Nat → Nat → Prop
rule lt.intro : le (succ m) n → lt m n

#eval add 2 3
#eval add ?x 2 = 5
#check le 2 4

theorem add_zero (n : Nat) : add n zero = n := by induction n
theorem le_refl (n : Nat) : le n n
theorem lt_succ (n : Nat) : lt n (succ n)
```

```text
$ horn examples/lang/nat.hn
add 2 3  ⟹  5
add 3 2 = 5  with ?x = 3
le 2 4  ✓
theorem add_zero : add n 0 = n  ✓ (by induction n)
theorem le_refl : le n n  ✓ (by induction n)
theorem lt_succ : lt n (succ n)  ✓ (by auto)
certificate accepted: …
```

## Declarations

| Form | Meaning |
| --- | --- |
| `sort S` | a sort |
| `ctor c : S₁ → … → S` | a constructor |
| `pred p : S₁ → … → Prop` | a predicate |
| `rule name : J₁ → … → J` | a Horn rule; lower-case names that are not symbols are its variables, and their sorts are inferred |
| `def f : S₁ → … → S` with clauses `\| p₁, …, pₙ => e` | a function |
| `theorem name (x y : S) : J₁ → … → J := by auto` or `by induction x` | a theorem, possibly with hypotheses; `:= by auto` may be omitted |
| `#eval J` or `#eval f a b` | a query: logic variables `?x` are solved, and a function call asks for its result |
| `#check J` | a ground judgment to derive |

A function `f : S₁ → … → Sₙ → S` is a predicate `f` with one more argument,
its result, and one rule per clause. A call in a clause's right-hand side
becomes a premise with a fresh result variable, so `succ (add m n)` in the
clause `succ m, n` gives the rule `add m n r → add (succ m) n (succ r)`.
`f a b = e` is notation for the judgment `f a b e`. Numerals stand for
`succ (… zero)` when the constructors `zero` and `succ` exist, and results
are printed back as numerals. Comments start with `--`.

## Proof search

Goals are solved by depth-first search with iterative deepening over, in
order, hypotheses, earlier theorems, the rules, and last earlier theorems
with hypotheses, whose hypotheses become subgoals. An
earlier theorem is used through an instance of its statement, so the
certificate refers to it rather than re-deriving it. `by induction x`
splits on the constructors of `x`'s sort; each case is searched with the
induction hypotheses for its recursive arguments. `by auto` searches, and if
that fails tries induction on each variable in turn.

Search is untrusted and incomplete: it can fail to find a proof, it never
makes one up. A function defined by overlapping or partial clauses is just a
relation; `#eval` reports the first result found.

## Implications

A theorem may have hypotheses: `theorem le_trans (a b c : Nat) : le a b → le b c → le a c`.
A function call nested in a statement becomes a hypothesis about a fresh
result, so `add m (succ n) = succ (add m n)` is proved as
`add m n = r → add m (succ n) = succ r`. See
[examples/lang/le.hn](../examples/lang/le.hn).

With hypotheses in scope, a goal is searched for with them; if that fails,
the prover does case analysis on a hypothesis, newest first and at most two
levels deep. It unifies the hypothesis with the conclusion of each rule for
its predicate: rules that cannot have derived it drop out, and each
remaining rule gives a case with its premises as new hypotheses. A
hypothesis no rule concludes, like `le (succ n) zero`, proves anything.

Induction on `x` keeps the hypotheses: each case assumes them at the
constructor, and the induction hypothesis is a rule from the hypotheses at
a recursive argument to the conclusion there, for all values of the other
variables. `le_trans` needs this: in the case `succ p` it applies the
induction hypothesis at a different `b` and `c`. A proved implication
becomes a lemma whose hypotheses are premises, for the hypotheses its proof
actually used.

In the certificate these are `hyp` steps for the hypotheses, `invert` steps
for case analysis, `induct` steps with hypotheses, and `apply` steps for the
use of a rule hypothesis or a lemma; the goal states its hypotheses. Case
analysis must give the same unifier the checker computes, so the prover
runs the checker's unification algorithm on the same terms. Each failed
attempt is rolled back, so the certificate holds only the proof found.

## What is checked

The run elaborates the theory to the kernel's input language and writes
goals and a schematic certificate (`--emit DIR` saves `theory.horn`,
`goals` and `proof`). `horn::schematic` then checks them; a theorem's
statement over its variables becomes a goal over eigenvariables, and
induction becomes an `induct` step. `--agda MODULE OUT.agda` exports the
certificate for the Agda model: [agda/NatLang.agda](../agda/NatLang.agda) is
the export of [examples/lang/nat.hn](../examples/lang/nat.hn) and is checked
by `nix flake check`.

What a rule says is still the author's responsibility, as for any Horn
theory: `rule bad : le (succ n) n` makes false things provable.

## Limits

- Certificates with implications are checked by `horn::schematic`, whose
  rules are proved sound at the level of the calculus in
  [agda/Implication.agda](../agda/Implication.agda), but the Agda export
  does not support them yet; `--agda` fails for such a file.
- Case analysis is at most two levels deep, and hypothetical goals get a
  smaller search budget.
- Induction is structural on one variable per proof, one level deep.
- No implicit arguments, notation, type classes or modules.
- The search is plain backtracking with a step budget per depth bound.

## Next steps

1. Exporting implications to the Agda model. The unification algorithm it
   needs is proved to give most general unifiers in
   [agda/Unify.agda](../agda/Unify.agda).
2. Nested induction and a small tactic language (`apply`, `cases`, `exact`).
3. Using a function's clauses as rewrite rules, so that `#eval` computes
   instead of searching.
