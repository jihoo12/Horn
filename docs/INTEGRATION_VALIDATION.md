# Standalone integration validation

## Initial replay increment

Validated 2026-10-18 (Asia/Seoul) on Linux x86_64, with an 8 GiB cgroup
memory limit. Nix 2.20.6, the repository's unchanged flake.lock,
Rust 1.91.1 / Cargo 1.91.0. No Cargo dependencies were added.

## Checks

- `cargo fmt --all -- --check` passed.
- `cargo clippy --locked --offline --all-targets -- -D warnings` passed.
- `cargo test --release --locked --offline`: 62 passed, 0 failed.
- The language suite covers nested forward computation, missing clauses,
  wrong sorts, unbound results, first-match commitment on a diverging clause,
  nullary functions, nonlinear patterns, relational search and induction.
  The pre-existing NatLang Agda export is byte-for-byte unchanged.
- A ground forward-computation certificate also replays through `kernel::Theory`
  directly, without the schematic induction/inversion route.
- The cubical suite checks the actual 185,673-step / two-goal U0 univalence
  certificate and 18,849-step ua-transport computation certificate. Corrupt and
  truncated oracles, the false `U0 : U0` goal, undeclared predicates, unknown
  example names and overwriting an export directory are rejected.
- CLI export produces ordinary theory/goals/oracle files independently
  accepted by the same generic checking API used by `oracle-kernel`.

`src/kernel.rs`, `src/lex.rs`, `src/sexp.rs`, `src/schematic.rs` and the Agda
models are unchanged from baseline `4fafc55`. This increment does not extend
either certificate calculus. Generic pipe/decode/check orchestration was
moved from `oracle-kernel` into `oracle::check` so both CLI routes use it.
The checked-in theory and goals match the import hashes in
`examples/cubical/PROVENANCE.json`.

## One runtime observation

After the release build, this command succeeded without kamo3 or an upstream
download:

```sh
target/release/horn cubical check all
```

```text
ACCEPT (cubical univalence): 2 goals, 185673 proof steps, 35830 oracle bytes
ACCEPT (cubical ua-transport): 1 goals, 18849 proof steps, 4086 oracle bytes
```

A single run through the Nix development-shell launcher took 2.665 seconds;
Linux reported maximum child RSS of 369,888 KiB (approximately 361 MiB).
These are one environment's observations, including launcher overhead, not a
cross-platform benchmark or a guaranteed upper bound. The encoded artifacts
are 35,830 and 4,086 bytes; checking still validates every reconstructed step.

## Initial scope

The initial replay increment did not re-run kamo3's expensive producers or repair their OOM test.
It supplied standalone replay of real evidence, plus bounded execution and
certification of ordinary source-language programs. The fresh producer and
core source increment below now extends that scope. All-level computational
univalence, a total dependent programming fragment and a native compiler
remain on the integration roadmap.
The import preserves the chosen mathematical specification; it does not prove
its semantic soundness. No new Agda soundness theorem is claimed here.


## Fresh generation increment

Validated 2026-10-18 (Asia/Seoul), with the same pinned Nix environment.

- `cargo test --release --locked --offline`: **73 passed, 0 failed**.
- `cargo fmt --all -- --check` and
  `cargo clippy --locked --offline --all-targets -- -D warnings` passed.
- Seven producer tests cover fresh universe-level identities, applications,
  beta/path computation, endpoint rules, mixed binder substitution and
  dimension-dependent contexts. Generation is followed by independent ground
  kernel replay. Forged goals and invented rules are rejected.
- Four source/CLI tests cover fresh inputs, malformed syntax, source bounds,
  false typing/equality goals, rule injection, duplicate names, non-overwriting
  export and independent `kernel` CLI replay. No snapshot is used for these
  fresh certificates.
- The complete suite still checks the bundled univalence and ua-transport
  oracles, ordinary language execution, induction and negative kernel cases.
- `kernel.rs`, `lex.rs`, `sexp.rs`, `schematic.rs`, the object theories and Agda
  models are byte-for-byte unchanged from `3e363a7`. No new Cargo dependencies.

The new release commands produced:

```text
horn cubical run examples/cubical/source/basics.hcu
ACCEPT (generated cubical): 9 goals, 75 proof steps

horn cubical run examples/cubical/source/binders.hcu
ACCEPT (generated cubical): 3 goals, 139 proof steps
```

Fresh generation uses the existing scoped-path theory only. The `.hcu` core
uses explicit annotations and separate de Bruijn namespaces; it has bounded
root reduction and syntactic type matching, not general conversion or the
final named-binder surface syntax. Face/composition/Glue/univalence generation,
the semantic soundness of the theory and source elaboration correctness remain
separate obligations. This does not claim to fix kamo3's large-producer OOM.

## Named binders and certified type conversion

Validated 2026-10-18 (Asia/Seoul) in the same pinned development environment.

- `cargo test --release --locked --offline`: **81 passed, 0 failed**.
- Formatting and `cargo clippy --locked --offline --all-targets -- -D warnings`
  passed.
- Named and explicitly indexed forms produce exactly the same fixed goals
  and evidence. Tests cover local shadowing, anonymous/named binder mixing,
  independent namespaces, binding-site context dependencies, duplicate scope
  names and out-of-scope references.
- Type-conversion tests independently replay explicit `type.conv` evidence
  for reducible expected/inferred types and function/path/universe heads.
  They reject corrupted goals, removed conversion steps, false types,
  universe cumulativity and unsupported equality transport. Both annotated
  operands are checked even when their erased terms are identical.
- No checker, object-theory, Agda model, dependency or flake pin changes were
  needed. This remains untrusted generation of evidence for the existing rules.

Actual release CLI runs and independent replay:

```text
horn cubical run examples/cubical/source/named.hcu
ACCEPT (generated cubical): 6 goals, 148 proof steps

horn cubical run examples/cubical/source/conversion.hcu --emit NEW_DIR
ACCEPT (generated cubical): 9 goals, 234 proof steps

kernel NEW_DIR/theory.horn NEW_DIR/goals NEW_DIR/proof
ACCEPT: 9 goals, 234 proof steps, 19677 bytes, 286 distinct terms
```

Conversion is bounded root beta/path computation in a common universe, not
full normalization under binders/constructors. The path fragment has no general
`eq.conv`; non-reflexive reductions whose equality type would need transport
are reported as unsupported before an invalid transitivity step is emitted.
Nested conversion obligations are bounded at 32. Source/semantic soundness and
the later face/system/composition/Glue migration remain separate work.
