# Horn

A small Rust checker for explicit derivation certificates in many-sorted,
first-order Horn theories. The caller supplies the theory and exact goals;
the certificate supplies rule applications and references to earlier steps.

The checker implements generic sorting and schema matching. Predicate names
have no built-in meaning. It does not search for proofs or implement a native
type theory, substitution engine, equality solver, or univalence primitive.

## What 0.3 adds: oracle certificates

A certificate can now be just the decisions the checker cannot make by
itself. The checker rebuilds the derivation top-down from the goals by
unification, reusing what it has already derived. The certificate names a
rule or an earlier judgment only where more than one fits, and supplies a
term only where unification leaves one open. An adaptive range coder stores
these decisions; a predictable one costs a fraction of a bit.

kamo3's largest certificate, 4.07 GB, becomes a **63,890-byte** oracle, about
the size of its 59,673-byte goals file. That is 63,000 times smaller than the
original and 850 times smaller than its compact form. It is checked in 3.5 s.
Every kamo3 certificate round-trips and is accepted. Decoding is untrusted: it
produces a compact certificate that the unchanged kernel checks, so neither
the trusted code nor the Agda proof changes. See [ORACLE.md](docs/ORACLE.md).

## Research: statements over every universe level

A prototype outside the trusted kernel checks *schematic* certificates:
judgments with eigenvariables, hypotheses, and structural induction over the
term algebra. `horn-generalize` turns an existing ground proof into one, and
any ground instance unfolds into an ordinary certificate for the unchanged
kernel. kamo3's univalence proof at U₀ holds for every level `L`, with a
few inductions on `max`; so do 49 other ordinary goals and all three large
certificates, including the 4 GB ua-unglue one. Its checking algorithm is
modelled and proved sound in [agda/Schematic.agda](agda/Schematic.agda), and
an accepted certificate can be exported for that model to re-check. See
[SCHEMATIC.md](docs/SCHEMATIC.md).

## What 0.2 changes

- **Hash-consed, streaming kernel.** Each distinct ground term is stored once
  and compared by index, and proofs are read incrementally. Memory follows the
  number of distinct subterms, not the file size. The separate chunked replay
  layer is no longer needed or trusted.
- **Compact certificates.** A step can omit its conclusion: the checker
  builds it from the rule, using bindings from premises and explicit
  `(?var TERM)` bindings. Shared terms can be named with `(def ?n TERM)`. The
  untrusted `horn-compress` tool rewrites ordinary certificates into this form.
- **Machine-checked soundness.** [agda/Soundness.agda](agda/Soundness.agda)
  proves in Agda, with no libraries or postulates, that a model of the
  checking algorithm accepts only certificates whose goals are derivable.

On kamo3's largest certificate (4.07 GB, 1.13 million steps), checking went
from 967 s and 746 MiB to 74 s and 64 MiB. After compression the certificate
is 54.6 MB (75× smaller) and checks in 0.79 s. Ordinary certificates kept their
former verdicts in differential testing and on every application certificate
checked. See [BENCHMARKS.md](docs/BENCHMARKS.md).

## Run

Requires Rust 1.88 or newer. There are no external crate dependencies.

```sh
cargo run --release --locked --offline --bin kernel -- \
  examples/nat.horn examples/nat.goals examples/nat.proof

cargo run --release --locked --offline --bin stream-kernel -- \
  examples/nat.horn examples/nat.goals examples/nat.proof
```

Both commands print `ACCEPT` on success; failures print `REJECT` and exit
nonzero. Both read the proof incrementally; `stream-kernel` is kept as a
compatibility name. To produce and check a compact certificate:

```sh
cargo run --release --locked --offline --bin horn-compress -- \
  examples/nat.horn examples/nat.proof /tmp/nat.compact.proof
cargo run --release --locked --offline --bin kernel -- \
  examples/nat.horn examples/nat.goals /tmp/nat.compact.proof
```

[examples/nat.compact.proof](examples/nat.compact.proof) shows the result:
`(step 1 plus-two (0))` with no stated judgment.

To encode an oracle certificate, then check it:

```sh
cargo run --release --locked --offline --bin horn-oracle -- encode \
  examples/nat.horn examples/nat.goals examples/nat.proof /tmp/nat.oracle
cargo run --release --locked --offline --bin oracle-kernel -- \
  examples/nat.horn examples/nat.goals /tmp/nat.oracle
```

`oracle-kernel` decodes in one thread and streams the result into the kernel
in another. To inspect the certificate an oracle stands for, write it out
with `horn-oracle decode THEORY GOALS ORACLE PROOF`.

## Library

```rust
use horn::kernel::Theory;

fn main() -> Result<(), String> {
    let theory = Theory::parse(include_str!("examples/nat.horn"))?;
    let report = theory.check(
        include_str!("examples/nat.goals"),
        include_str!("examples/nat.proof"),
    )?;
    assert_eq!(report.goals, 1);
    Ok(())
}
```

The example paths above assume the Rust source file is at the repository root.
For a local downstream dependency, use `horn = { path = "../Horn" }`.
For Git dependencies, pin a reviewed commit with `rev`.

## Format and trust

See [FORMAT.md](docs/FORMAT.md) for the concrete input language and
[TRUST.md](docs/TRUST.md) for the acceptance contract and replay invariants.
The implementation has not been formally verified. Acceptance establishes
derivability relative to the supplied rules; it does not establish that those
rules correctly describe an intended mathematical theory.

## Development

```sh
cargo fmt --all -- --check
cargo clippy --locked --offline --all-targets -- -D warnings
cargo test --locked --offline
cargo test --release --locked --offline
nix flake check   # Rust build and tests, plus both Agda soundness proofs
```

All commands above run using this repository alone; no kamo3 checkout or
credentials are required.

Optional application compatibility checks require access to **kamo3, a private
research repository**. If you already have an authorized checkout, you can
check its original cubical snapshots without importing its theory or producers:

```sh
bash scripts/check-kamo3.sh /path/to/kamo3
```

This checks all 19 ordinary deep snapshots (77 goals). It then compresses
each one and checks the compact version, and encodes each one as an oracle and
checks that. It requires `gzip`; large proofs identified only by hashes are not
regenerated. Their generation remains an application responsibility.

See [BENCHMARKS.md](docs/BENCHMARKS.md) for the standalone measurement tool and
recorded application results. The recorded cubical workloads are private, so
those measurements cannot currently be independently reproduced from Horn alone.

## Origin and direction

Extracted from the private [kamo3](https://github.com/jihoo12/kamo3) repository at commit
`6a226630910b34ac89dc77f08a22fe956340aecf`. The extraction preserved the core
files byte-for-byte; subsequent parser optimization is covered by differential
tests against that baseline. Cubical rules, certificate producers,
Agda references, and mathematical research remain in kamo3. Upstream links are
provenance references for authorized readers; access is not required to use or
review Horn's implementation, input format, trust contract, or standalone tests.

[PROVENANCE.md](docs/PROVENANCE.md) records the extraction boundary.
[VALIDATION.md](docs/VALIDATION.md) records the checks performed at extraction.
[ROADMAP.md](docs/ROADMAP.md) describes formal verification and performance
work. The initial extraction preserved the algorithm and file formats as a
comparison baseline for subsequent optimizations.

Licensed under [Apache-2.0](LICENSE).
