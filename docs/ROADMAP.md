# Next work

## Verification

Freeze the accepted language and checker semantics. Mechanize that acceptance
implies a finite ground Horn derivation, connect the model to the executable
implementation, and include replay and its scratch-file admission discipline.
Keep downstream theories' adequacy and semantic soundness as separate duties.

## Performance

Preserve this extraction as a behavioral baseline. Measure release builds,
peak RSS, parsing, sorting, schema matching, serialization, and replay imports.
Separate certificate production from checking and compare both valid and
adversarial certificates when changing the checker.

Initial candidates, in approximate investigation order:

1. Implemented: avoid per-token string allocation and duplication in the parser;
   retain the extraction parser as a test-only differential reference.
2. Avoid deep copies when binding schema variables and retaining judgments.
3. Remove parse/serialize/reparse cycles in replay while preserving admission
   invariants and the exact caller-selected theory and goals.
4. Share identical subterms using collision-safe structural identities; assess
   both kernel and untrusted producer representations.
5. Tune chunk sizes using multiple representative workloads.
6. Evaluate compiled rule matching after measuring the remaining bottlenecks.

An exploratory profile before extraction used the upstream `compute` snapshot
(39,657,410 bytes; 77,170 steps). An optimized, temporarily instrumented build
took about 4.68 s and 2.43 GiB peak RSS in ordinary mode, versus 7.90 s and
449 MiB with 4 MiB replay chunks. Ordinary parsing accounted for about 2.03 s
and schema matching for 0.60 s. These are single-run observations on one
machine, not reproducible performance guarantees or optimized implementation
results. Large 762 MB and 4 GB certificates were not profiled in this study.

Structural counting found 15,378,980 judgment-tree nodes but 81,340 distinct
subtrees in `compute`, and 52,232,722 versus 66,241 in `equiv-ext`. These counts
suggest sharing opportunities; they do not predict memory or speedup ratios.

Compiling rules cannot eliminate the obligation to validate every admitted
step. Trusting generated native checkers introduces a compiler-correctness
obligation; retaining a small source checker alone does not discharge it.

## Application integration

Migrate kamo3 to a pinned Horn dependency after checking its ordinary and large
certificates. Keep cubical rules and producers outside this repository. Add
generic stress fixtures and a repeatable benchmark harness before setting
performance targets. A general proof search engine is not part of the checker.
