# Next work

The active product direction is the staged [language and cubical integration](INTEGRATION.md).
Keep the generic kernel independent of both, and distinguish the existing
[standalone replay package](CUBICAL.md) from migration of source elaboration.

## Verification

Done: [agda/Soundness.agda](../agda/Soundness.agda) mechanizes that acceptance
by a tree model of the checking algorithm, including inferred conclusions and
explicit bindings, implies a finite ground Horn derivation of every goal.

Remaining, in order:

1. Add sorts to the model and prove that every instance used is well sorted.
2. Model `def` expansion and the textual reader.
3. Prove the hash-consing refinement: indices issued by `make` are in
   bijection with well-sorted trees, so index comparison decides tree equality.
4. Connect the model to the executable, for example by extracting the Agda
   checker and running it differentially against the Rust kernel on the
   application corpus, or by verifying the Rust code against the model.

Keep downstream theories' adequacy and semantic soundness as separate duties.

## Performance

Done in 0.2: items 2–4 of the original list. Terms are hash-consed, so
matching binds indices instead of copying trees; replay's parse, serialize
and reparse cycle is gone because the kernel streams; identical subterms are
shared with collision-safe structural identities. Chunk tuning (item 5) no
longer applies. See [BENCHMARKS.md](BENCHMARKS.md).

Remaining candidates:

1. Interning dominates on ordinary certificates (about 55 MB/s). A faster
   table or fewer random memory accesses per node would help large ordinary
   inputs. Compact and oracle certificates are already small enough not to
   need it.
2. Producers could emit oracle certificates directly. A producer that already
   searches top-down would only record its choices. This would remove both the
   multi-gigabyte intermediate file and the encoding pass.
3. Oracle decoding (3.5 s, 399 MiB on ua-unglue) is now slower than checking
   the compact form. Unifying against indexed candidates instead of trying
   every rule, and releasing tables early, are the obvious next steps.
4. Specify oracle version 1 independently of `src/oracle.rs` so that a second
   implementation could decode it.
5. Evaluate compiled rule matching only after measuring a workload where
   matching, rather than reading, dominates.

Compiling rules cannot eliminate the obligation to validate every admitted
step. Trusting generated native checkers introduces a compiler-correctness
obligation; retaining a small source checker alone does not discharge it.

## Application integration

kamo3 pins Horn commit `212a641` (kamo3 commit `ca123f6`). Version 0.2 keeps
the `kernel`, `replay` and `sexp` APIs and both binary names, and accepts every
stored certificate unchanged (see [VALIDATION.md](VALIDATION.md)); upgrading
the pin still requires the application's own checks. `Report` gained two
public fields, which matters only to code that constructs it.

Keep cubical rules and producers outside this repository. A self-contained
representative workload generator would let external readers reproduce the
performance studies without access to the private application inputs.
General proof search stays outside the ground checker; the surface-language
frontend already provides bounded search and certified forward execution.
