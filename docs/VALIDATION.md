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

## Parser optimization

The borrowed-token parser at `212a641` passed formatting, all-target clippy
with warnings denied, and all 14 integration tests in debug and release.
Two new parser tests compare exact trees and errors with the extraction parser
for 66,430 exhaustive short inputs and additional comment, Unicode, line-ending,
and depth-boundary cases. The reference parser exists only under `tests/support`.

Five end-to-end samples per input and mode were collected for both the baseline
and optimized parser. See [BENCHMARKS.md](BENCHMARKS.md) for the procedure,
results, input digests, and raw samples. The larger application proofs and Agda
remain outside this measurement.

Both optimized checkers also accepted all 19 original ordinary deep snapshots,
77 fixed goals per checker, using `scripts/check-kamo3.sh`.

Downstream integration in kamo3 commit `ca123f6` pins `212a641`, removes the
embedded implementation, and preserves the existing API through re-exports.
All 109 application tests and all-target clippy passed. Its Nix deep-certificate
check also passed: release tests, regeneration of all 19 ordinary certificates,
snapshot comparison, and acceptance of all 77 fixed goals. Nix fetches the exact
lockfile Git revision using the authenticated user environment before sandboxed
builds, so private-repository credentials are not needed inside the builders.
