# Acceptance contract and trust boundary

For a fixed many-sorted Horn theory H and caller-selected ground goals G,
the intended guarantee is: if checking succeeds, every goal in G has a finite
derivation using ground instances of rules in H.

For each step the checker verifies consecutive numbering, an existing rule,
the exact premise count, earlier-only references, and one consistent schema
assignment across the premises, any explicit bindings, and any stated
conclusion. A stated conclusion must be well sorted; an omitted one is built
by instantiating the rule, which fails if a conclusion variable is unbound.
Each result must exactly match a caller-selected goal, and all goals must be
reported exactly once. The proof cannot introduce declarations or rules.

## Mechanized soundness

[agda/Soundness.agda](../agda/Soundness.agda) models the checking algorithm
on plain trees and proves in Agda that acceptance implies a derivation of
every goal from ground instances of the rules:

```agda
soundness : (R : List Rule) (goals : List Term) (c : Certificate)
          → accepts R goals c ≡ just tt → All (Derivable R) goals
```

The model includes stated and inferred conclusions, explicit bindings,
schema matching against one assignment, earlier-only references, and goal
results. It is checked with `--safe --without-K --no-libraries`, so it uses no
postulates and no library code; `nix flake check` runs it. The file also
evaluates the model on the natural-number example in ordinary and compact form.

The model is not connected to the Rust code by a proof. Not modelled: textual
parsing, names, sorts (derivations in the model are unsorted; that every
instance used is well sorted rests on the Rust sort checks), `def` abbreviations (which
the Rust reader expands while parsing), and hash-consing. The Rust kernel is
written to follow the model step for step, and differential tests compare it
with the extraction-time kernel on random and mutated inputs.

## Hash-consed terms

The kernel stores every distinct ground term and judgment once in an arena and
refers to it by index. Two invariants carry the soundness argument over from
trees to indices:

1. **Well-sortedness by construction.** `Arena` nodes are created only through
   `Checker::make`, which checks the symbol's arity and every argument's sort.
   Every index therefore denotes a well-sorted ground term or judgment.
2. **Index equality is structural equality.** A node is a head symbol plus
   argument indices. Interning compares the complete node with the stored one;
   the hash only selects a probe position. Distinct terms can never share an
   index, regardless of hash collisions, and equal terms always do because
   their arguments already do (induction on term height).

With these, matching a variable against a term, comparing a binding, and
comparing a result to a goal are each one integer comparison, and the cost of
matching a rule is proportional to the size of its schemas.

Adversarial inputs can force hash collisions and slow checking down; they
cannot change a verdict.

## Components

- `src/kernel.rs`: theory validation, sorting, hash-consing, matching,
  instantiation, reference and goal checks.
- `src/lex.rs` and `src/sexp.rs`: the one lexer used for theories, goals and
  proofs, and the S-expression reader for theories.
- `src/bin/kernel.rs`, `src/bin/stream-kernel.rs`: input and execution
  boundary; both read proofs incrementally.
- `src/replay.rs`: a compatibility wrapper around `check_reader`. The former
  chunked replay layer, with its scratch-file admissions and reserialization,
  is no longer part of the trusted code.
- Selected theories and goals: caller-controlled mathematical specification.
- Rust compiler, libraries, operating system, hardware, and execution environment.

Certificate producers do not need to be trusted for logical acceptance. This
includes `src/compress.rs` and `horn-compress`. It also includes oracle
certificates: `src/oracle.rs`, `horn-oracle`, and the decoding thread of
`oracle-kernel`. That thread only writes a compact certificate into a pipe,
and the kernel reads and checks the certificate as it would a file (see
[ORACLE.md](ORACLE.md)). An incorrect or inconsistent
supplied theory can still derive its consequences; the checker does not
validate its intended semantics or consistency.

## Limits

Tests and the Agda model do not prove the Rust implementation correct.
Decoding an oracle takes time and memory proportional to the derivation it
expands to, which can be far larger than the oracle itself. Memory
is proportional to the number of steps and distinct subterms, which is small
for the certificates measured but not bounded by a constant. Parsing limits
do not provide complete resource isolation.

No semantic soundness theorem for a downstream type theory, normalization
result, or consistency result follows solely from certificate acceptance.
