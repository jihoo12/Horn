# Extraction validation — 2026-10-16

Horn's standalone tests and examples are included in this repository. The
application checks reported below were performed by the maintainer using the
private kamo3 checkout. Those inputs and downstream source are not included
here, so external readers cannot reproduce the application-specific checks
from Horn alone. These results supplement the standalone tests; they are not
prerequisites for building or testing Horn.

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
- `bash scripts/check-kamo3.sh /path/to/kamo3`: all 19 ordinary deep
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

## Hash-consed kernel, compact certificates and Agda proof — 2026-10-17

- `cargo fmt --check`, all-target clippy with warnings denied, and all
  integration tests in debug and release passed.
- Differential tests against the extraction-time kernel (kept under
  `tests/support`): 60,000 random certificates, half token-mutated, in a mix
  of ordinary and compact forms; compact forms are expanded by an independent
  tree-based reference before the legacy kernel checks them. Verdicts agreed in
  every case, ordinary certificates kept their former verdict, and every
  accepted ordinary certificate stayed accepted after `compress`. A further
  80,000 mutated theories received the same parse verdict from both kernels.
- The exhaustive parser comparison (66,430 inputs) passed with the new shared
  streaming lexer underneath `sexp::parse`.
- `scripts/check-kamo3.sh`: all 19 stored snapshots accepted (77 goals), and
  all 19 compressed versions accepted.
- The 4 GB `ua-unglue` and 762 MB `constant-equiv` certificates were
  regenerated, matched kamo3's recorded digests, and were accepted as stored
  and after compression; the old `stream-kernel` accepted both as well.
- `nix flake check`: the sandboxed Rust build with tests and the Agda proof
  passed. Changing the Agda file to claim acceptance of a wrong certificate
  fails with `nothing != just tt`, as expected.

Minimum-version Rust 1.88 and hosted CI were not tested locally.
