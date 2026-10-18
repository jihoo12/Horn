# One Horn repository, separate trust boundaries

Horn is to become a language in which programs and proofs can be developed
alongside cubical mathematics. Keep one repository for now; a new kamo4
repository would create another integration boundary before the existing one
has been removed. kamo3 remains an upstream research archive during migration.

## Boundaries

1. **Generic checking.** Keep the ground kernel independent of object theories,
   evaluation, elaboration, and proof search. Do not give predicate names such
   as `transport` or `ua` built-in meanings. Changing the kernel requires a
   generic correctness argument and rejection tests, not just a faster example.
2. **Certificate languages.** Ground and schematic certificates are distinct
   verification routes. Surface-language induction uses the schematic checker;
   cubical ground certificates use the ground checker. Neither acceptance
   contract can silently stand in for the other. The Agda models are not a
   formal verification of the Rust implementations.
3. **Language tools.** Parsing, elaboration, pattern-match execution, search,
   tactics, and future compilation produce evidence. They do not extend the
   checking rules. A faster evaluator must still certify its reported result.
4. **Object theories.** Cubical rules and fixed mathematical goals are explicit
   data with provenance and limitations. Loading a theory is a mathematical
   specification choice. It is not an assertion that the rules have a complete
   semantic soundness proof. No example certificate may install its own axioms.

These boundaries start as modules, data directories, and acceptance tests.
Split crates when a real dependency boundary needs enforcement; do not churn
the public library API just to give the directories architectural names.

## First integration increment

- Make forward, ground function evaluation follow the declared clauses and
  produce a checked certificate. Retain relational search for logic queries.
  Keep resource limits and report partial or diverging evaluation honestly.
- Bring a fixed, attributed cubical theory and real U0 univalence and
  judgmental ua-transport certificates into this repository. Oracle decoding
  remains untrusted and streams ordinary steps into the unchanged kernel.
- Require standalone commands, positive checks, wrong-goal and corrupted-proof
  rejection, and no checkout or runtime download from kamo3.

This is a runnable bridge, not a complete cubical source language or a new
implementation of Lean 4. Replaying a frozen proof is not constructing a new
proof, and level-generic schemas are not internally universe-polymorphic terms.

## Current producer migration

The first fresh generator is now Horn-owned: `cubical::producer` certifies
universes, dependent functions, both substitutions and scoped dependent paths
against the unchanged path-theory fragment. `horn cubical run FILE.hcu`
reads an explicit annotated core source file, fixes its requested judgments,
generates new evidence and asks the ground kernel to check it. Exported data
can be replayed independently. See [CUBICAL_PRODUCER.md](CUBICAL_PRODUCER.md).

The prefix core source now accepts named ordinary/dimension binders and named
contexts, elaborating them to the same de Bruijn core. Bounded root beta/path
type conversion emits explicit equality and `type.conv` evidence; reducible
function/path/universe heads are exposed with checked typing transport.
General congruence, equality transport across converted types, fresh
face/composition/Glue/univalence producers and connection to the `.hn`
programming frontend remain open. The theories, ground/schematic checkers and Agda models are unchanged.

## Following increments

1. Move cubical certificate producers behind a Horn-owned library API, one
   feature at a time. The bounded contexts/universes/functions/substitution/path
   generator is implemented; continue with faces, systems, composition, Glue
   and ua. Named binders and bounded root conversion are implemented; stronger
   conversion still requires explicit congruence/equality-transport evidence.
   Keep imported snapshot replay as an independent migration oracle. Do not
   copy the entire research frontend without checking its assumptions.
2. Add source modules/imports, dependent binders and diagnostics; elaborate
   new source-level cubical examples into the selected theory. Keep ordinary
   data programming useful in its own right. A total proof fragment needs
   coverage, non-overlap, positivity and termination checks before claiming
   Lean-like total-function semantics. Partial runtime computation needs a
   separate, explicit contract.
3. Generate compact/oracle evidence directly so checking does not require
   materializing multi-gigabyte intermediate proofs. Track generation memory
   separately from checker memory; kamo3's deep-univalence test exceeds the
   current 8 GiB environment even in release mode.
4. Export implicational certificates to the Agda model, support multiple
   universe variables and dependent computation, and connect the executable
   checkers to their models. Prove adequacy/soundness of the cubical encoding
   separately from generic Horn derivability.
5. Add a compiler/runtime, effects and interactive tooling only with explicit
   semantics and a clear distinction between running a program and proving a
   proposition. Native execution must not become a proof-checking shortcut.

A release should list which of these behaviors it actually supports. Keep
kamo3 until its relevant producers, rejection tests and Agda reference checks
have equivalents here. A new repository is justified later by independently
versioned tooling, not by the name of a research iteration.
