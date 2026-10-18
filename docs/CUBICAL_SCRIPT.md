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

## Forms

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
fixed at 0 for the prelude. Data types are the fixed bool and nat; there are no user-declared data types, no
implicit arguments and no modules. This format and the `.hcu` core files
and `.hn` programs are still separate frontends.
