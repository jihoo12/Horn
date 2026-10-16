# Horn

A small Rust checker for explicit derivation certificates in many-sorted,
first-order Horn theories. The caller supplies the theory and exact goals;
the certificate supplies rule applications and references to earlier steps.

The checker implements generic sorting and schema matching. Predicate names
have no built-in meaning. It does not search for proofs or implement a native
type theory, substitution engine, equality solver, or univalence primitive.

## Run

Requires Rust 1.88 or newer. There are no external crate dependencies.

```sh
cargo run --release --locked --offline --bin kernel -- \
  examples/nat.horn examples/nat.goals examples/nat.proof

cargo run --release --locked --offline --bin stream-kernel -- \
  examples/nat.horn examples/nat.goals examples/nat.proof
```

Both commands print `ACCEPT` on success; failures print `REJECT` and exit
nonzero. The ordinary CLI reads the whole proof into memory. The streaming
CLI uses 4 MiB chunks and a private temporary file. Chunked replay reduces
memory use but adds work and additional trusted code. Oversized input forms
may be rejected by the streaming path even when the ordinary path accepts.

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
```

To check the original cubical certificate snapshots without importing their
theory or producers into this repository:

```sh
bash scripts/check-kamo3.sh /path/to/kamo3
```

This runs both checkers on all 19 ordinary deep snapshots (77 goals per
checker). It requires `gzip`; large proofs identified only by hashes are not
regenerated. Their generation remains an application responsibility.

## Origin and direction

Extracted from [kamo3](https://github.com/jihoo12/kamo3) at commit
`6a226630910b34ac89dc77f08a22fe956340aecf`. The three core implementation
files are copied without changes. Cubical rules, certificate producers,
Agda references, and mathematical research remain in kamo3.

[PROVENANCE.md](docs/PROVENANCE.md) records the extraction boundary.
[VALIDATION.md](docs/VALIDATION.md) records the checks performed at extraction.
[ROADMAP.md](docs/ROADMAP.md) describes formal verification and performance
work. This initial extraction deliberately preserves the existing algorithm
and file formats so future optimizations have a stable comparison point.

Licensed under [Apache-2.0](LICENSE).
