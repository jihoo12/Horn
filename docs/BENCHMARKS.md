# End-to-end checker benchmarks

Build `cargo build --release --locked --offline --example benchmark`, then run:

```sh
target/release/examples/benchmark THEORY GOALS PROOF 5 > results.csv
```

Every row is a fresh child process that checks the requested goals. A failed
check fails the benchmark. Ordinary and 4 MiB streamed modes alternate order
between repetitions. The timer includes input reads, theory parsing, checking,
and cleanup of the main proof/theory values; it excludes process startup and
the subsequent RSS query. Peak RSS is Linux `/proc/self/status`'s `VmHWM`, in
KiB. On other platforms the RSS field is empty. Samples include filesystem
cache effects; no attempt is made to flush system caches. Run competing builds
sequentially on the same idle machine and report medians and raw samples.

For representative application inputs from a kamo3 checkout:

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
