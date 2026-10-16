# End-to-end checker benchmarks

Build `cargo build --release --locked --offline --example benchmark`, then run:

```sh
target/release/examples/benchmark THEORY GOALS PROOF 5 > results.csv
```

The harness works with any suitable theory, goals, and certificate. For a small
self-contained smoke test using only this repository:

```sh
target/release/examples/benchmark examples/nat.horn examples/nat.goals examples/nat.proof 5
```

This tiny fixture verifies the harness; it is not representative of large-proof
performance and does not reproduce the cubical results below.

Every row is a fresh child process that checks the requested goals. A failed
check fails the benchmark. Ordinary and 4 MiB streamed modes alternate order
between repetitions. The timer includes input reads, theory parsing, checking,
and cleanup of the main proof/theory values; it excludes process startup and
the subsequent RSS query. Peak RSS is Linux `/proc/self/status`'s `VmHWM`, in
KiB. On other platforms the RSS field is empty. Samples include filesystem
cache effects; no attempt is made to flush system caches. Run competing builds
sequentially on the same idle machine and report medians and raw samples.

The recorded application workloads come from **kamo3, a private research
repository**. Its theory, goals, and certificate snapshots are not distributed
with Horn. External readers can inspect the raw results and input digests, but
cannot independently reproduce those exact measurements from this repository
alone. The digests identify the measured inputs; they do not supply them.

The following script is optional and requires an authorized kamo3 checkout:

```sh
bash scripts/benchmark-kamo3.sh /path/to/kamo3 /tmp/horn-results 5
```

The script prepares the original deep theory and the `ua-beta` and `compute`
snapshots, then records CSVs, input SHA-256 digests, compiler/platform details,
and Git state in the output directory. Certificate generation is excluded.
Allow enough RAM for the ordinary checker. The input files remain in the output
directory for reuse. They are not part of this repository.

The benchmark executable can also be copied unchanged to another Horn revision
and compiled there. This keeps the measurement procedure identical for before
and after comparisons. This harness is development tooling, outside the trusted
checker.

## Borrowed-token parser — 2026-10-16

Compared baseline `903fe27` with parser change `212a641`, using the same
benchmark executable source and five repetitions per mode/input on the same
x86_64 Linux machine (rustc 1.95.0). Baseline runs completed before optimized
runs; other builds and checking workloads were kept out of the timing window.
Report the median elapsed time and median process peak RSS separately:

| Input | Mode | Time before → after | Peak RSS before → after |
| --- | --- | --- | --- |
| ua-beta (26,107,428 bytes) | Ordinary | 3.085 → 2.102 s | 1,713 → 879 MiB |
| ua-beta | Streamed | 5.849 → 4.794 s | 460 → 294 MiB |
| compute (39,657,410 bytes) | Ordinary | 4.639 → 3.689 s | 2,488 → 1,276 MiB |
| compute | Streamed | 7.825 → 6.700 s | 449 → 266 MiB |

Ordinary elapsed time fell 20–32% and peak RSS about 49%. Streamed elapsed
time fell 14–18% and peak RSS 36–41%. These are measured changes for these
inputs, not a general speed guarantee or a claim about certificate production.
The approximately 762 MB and 4 GB application proofs were not benchmarked.

The parser now lexes borrowed input slices on demand instead of allocating an
intermediate vector of owned token strings. It still returns the same owned
syntax tree. Rule matching, sorting, goal checks, and replay are unchanged.
Tests compare exact parsed trees and error strings against the extraction
parser for 66,430 short inputs and additional Unicode/comment/depth cases.
The old parser is retained only as a test reference.

Raw CSVs and environment records are in
[benchmarks/parser-2026-10-16](benchmarks/parser-2026-10-16).
Input hashes (the theory is the concatenation prepared by the script):

```text
da7a1011db76ba7f6ae444f822692352a8747c2b0ac9b6e946eb154282b377ce  deep.horn
825a8c976e8e3fa722447991e12e851bf78e49036c7b4cdc27a34d27d8b550b6  ua-beta.goals
c78ece1b597ee42ca850e0d588e0a8a220395354a0ec319222f262705bc56416  ua-beta.proof
7179737066b9618735504efe7a441e104ff220d1de8453010369aab5a635cbe2  compute.goals
47f1d213eec69fd6cc73a69bfe842346cc3a7082bad7d507535f92decd4851fa  compute.proof
```

## Hash-consed streaming kernel — 2026-10-17

Same machine, compiler, harness source and inputs (identical SHA-256 digests
to the parser study above). Five samples per mode; medians. "Streamed" now
means `replay::check`, which calls the incremental kernel; "ordinary" still
reads the whole proof into one string first, so its RSS includes that text.

| Input | Mode | `212a641` → 0.2 time | Peak RSS |
| --- | --- | --- | --- |
| ua-beta (26,107,428 bytes) | Ordinary | 2.102 → 0.513 s | 879 → 30.3 MiB |
| ua-beta | Streamed | 4.794 → 0.498 s | 294 → 5.5 MiB |
| compute (39,657,410 bytes) | Ordinary | 3.689 → 0.772 s | 1,276 → 44.9 MiB |
| compute | Streamed | 6.700 → 0.739 s | 266 → 7.3 MiB |

Raw CSVs: [benchmarks/kernel-2026-10-17](benchmarks/kernel-2026-10-17).

### Large application certificates

The two largest kamo3 certificates were regenerated with kamo3's own producers
at its pinned revision; both matched the SHA-256 digests kamo3 records
(`cdce07b9…` and `6f189902…`). Single runs measured with GNU time, wall clock
and maximum RSS, one job at a time. "Old" is the `stream-kernel` binary built
from `212a641`; "new" is the 0.2 `kernel` reading the same file incrementally.

| Certificate | Old stream-kernel | New, as stored | Compact size | New, compact |
| --- | --- | --- | --- | --- |
| ua-unglue (4,067,276,087 bytes, 1,128,752 steps) | 967.0 s, 746 MiB | 74.3 s, 64 MiB | 54,591,519 bytes | 0.79 s, 66 MiB |
| constant-equiv (761,517,734 bytes, 530,397 steps) | 183.1 s, 660 MiB | 13.9 s, 34 MiB | 24,273,371 bytes | 0.32 s, 34 MiB |

`ua-unglue` contains 1,174,890 distinct terms and judgments; `constant-equiv`
538,502. Compressing took 225.8 s / 472 MiB and 40.8 s / 225 MiB with the
unoptimized `horn-compress`; that cost belongs to production, not checking.

### Compression of the stored snapshots

`horn-compress` output for all 19 stored snapshots was accepted for every goal
(`scripts/check-kamo3.sh`). Largest cases:

| Snapshot | Ordinary bytes | Compact bytes | Ratio | Unused steps dropped |
| --- | --- | --- | --- | --- |
| ua-unglue-center | 186,225,018 | 4,504,943 | 41× | 0 |
| equiv-ext | 119,438,460 | 2,643,166 | 45× | 0 |
| glue-fiber | 70,792,538 | 3,111,017 | 23× | 4,025 |
| compute | 39,657,410 | 3,076,975 | 13× | 4,453 |
| ua-beta | 26,107,428 | 1,589,886 | 16× | 1,424 |

Several application certificates contain steps that no result uses; the
kernel still checks them in the ordinary form, and the compressor drops them.
These are measurements of these inputs on one machine, not general guarantees.
