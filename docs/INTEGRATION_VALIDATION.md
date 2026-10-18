# Standalone integration validation

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

## Scope

This does not re-run kamo3's expensive producers or repair their OOM test.
It supplies standalone replay of real evidence, plus bounded execution and
certification of ordinary source-language programs. The cubical source
elaborator, producers, all-level computational univalence, a total dependent
programming fragment and a native compiler remain on the integration roadmap.
The import preserves the chosen mathematical specification; it does not prove
its semantic soundness. No new Agda soundness theorem is claimed here.
