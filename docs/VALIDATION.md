# Extraction validation — 2026-10-16

Validated locally on x86_64 Linux with rustc 1.95.0. The implementation baseline
is kamo3 commit `6a226630910b34ac89dc77f08a22fe956340aecf`.

- Core source files compared byte-for-byte with the source checkout; hashes
  are recorded in [PROVENANCE.md](PROVENANCE.md).
- `cargo fmt --all -- --check`: passed.
- `cargo clippy --locked --offline --all-targets -- -D warnings`: passed.
- `cargo test --locked --offline`: all 12 integration tests passed.
- `cargo test --release --locked --offline`: the same 12 tests passed.
- Both documented natural-number CLI commands: accepted the fixed goal.
- `bash -n scripts/check-kamo3.sh`: passed.
- `bash scripts/check-kamo3.sh /home/jihoo/kamo3`: all 19 ordinary deep
  snapshots accepted by each checker, 77 fixed goals per checker.

The compatibility run used the original theory fragments and stored snapshots;
it did not regenerate application certificates. The approximately 762 MB
constant-equivalence and 4 GB ua-unglue proofs, which are represented upstream
by digests rather than snapshots, were not regenerated or replayed. Agda was
not run. Minimum-version Rust 1.88 and hosted CI were not tested locally.

These checks establish an extraction baseline; they do not constitute formal
verification or demonstrate an optimization speedup.
