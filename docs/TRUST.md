# Acceptance contract and trust boundary

For a fixed many-sorted Horn theory H and caller-selected ground goals G,
the intended guarantee is: if checking succeeds, every goal in G has a finite
derivation using ground instances of rules in H.

For each step the ordinary checker verifies consecutive numbering, an existing
rule, a well-sorted ground conclusion, the exact premise count, earlier-only
references, and one consistent schema assignment across conclusion and premises.
Each result must exactly match a caller-selected goal, and all goals must be
reported exactly once. The proof cannot introduce declarations or rules.

An induction on step number explains the intended soundness argument. Each
accepted zero-premise step instantiates a rule of H; every other step combines
previously established derivations using an instance of a rule of H. This is
an informal argument, not a machine-checked refinement theorem for this Rust
implementation.

## Components

- `src/kernel.rs`: theory validation, sorting, matching, reference and goal checks.
- `src/sexp.rs`: parsing and syntax representation.
- `src/bin/kernel.rs`: ordinary input and execution boundary.
- `src/replay.rs` and `src/bin/stream-kernel.rs`: additional trusted code for
  streamed admission, scratch storage, and final results.
- Selected theories and goals: caller-controlled mathematical specification.
- Rust compiler, libraries, operating system, hardware, and execution environment.

Certificate producers do not need to be trusted for logical acceptance.
An incorrect or inconsistent supplied theory can still derive its consequences;
the checker does not validate its intended semantics or consistency.

## Replay invariants

1. Original steps remain sequential; references point backward.
2. Input certificates may call only rules of the original theory.
3. Cross-chunk premises are imported only from facts admitted by earlier,
   fully checked chunks. Existing scratch bytes are discarded at startup.
4. Imported facts become temporary ground zero-premise rules with a private
   name prefix that avoids original rule names. Input cannot invoke these rules.
5. All steps of a chunk pass the ordinary checker before any are admitted.
6. Final results are checked against the original caller-selected goals.

Imported facts abbreviate already checked derivations. An induction over chunks
therefore gives the intended reduction to derivations in the original theory.
The implementation of that reduction remains part of the trust boundary.

## Limits

Tests do not prove universal soundness. Parsing limits and chunking do not
provide complete resource isolation. Whole-proof checking may consume far more
memory than the text size. Streaming stores verified facts on disk and keeps
in-memory metadata proportional to the number of steps; imports and syntax
expansion also consume memory. This is not a constant-memory checker.

No semantic soundness theorem for a downstream type theory, normalization
result, or consistency result follows solely from certificate acceptance.
