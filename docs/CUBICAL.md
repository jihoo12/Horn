# Standalone cubical certificate package

Horn now carries an explicit cubical theory and two real certificates from
kamo3. Checking them needs this repository alone. No checkout, credentials,
network download, or native cubical operation is required at runtime.

```sh
cargo run --release --locked --offline --bin horn -- cubical list
cargo run --release --locked --offline --bin horn -- cubical check all
```

| Example | Fixed goals | Checked steps | Oracle bytes |
| --- | ---: | ---: | ---: |
| `univalence` | 2 | 185,673 | 35,838 |
| `ua-transport` | 1 | 18,849 | 4,094 |
| `canonicity` | 3 | 231,279 | 51,822 |

`univalence` checks univalence at U0,
`Π A B:U₀. Equiv (Path U₀ A B) (Equiv A B)`, and that its function component
is the canonical map from paths to equivalences. It is the deep syntax
certificate, not the separate semantic-lemma theory that assumes the needed
mathematics in its premises.

`ua-transport` checks the typed judgmental equation
`transportⁱ (ua e i) x ≡ transportᵏ B (transportⁱ B (e x))` obtained using
Glue composition. There is no assumed judgmental regularity eliminating the
two constant transports. This is evidence for computational behavior in the
selected rules, not a general implementation of computational univalence at
all universe levels.

`canonicity` checks, in the empty context, that `not = λb. bif bool bfalse btrue b`
is an equivalence (by the closed isoToIsEquiv lemma) and that
`transport (ua not) btrue ≡ bfalse` and `transport (ua not) bfalse ≡ btrue`
at type `bool`. Transport along ua computes all the way to a boolean literal:
Glue composition, then bool's composition, which returns its base. That rule
is sound because bool is discrete (the constant presheaf 2 in the cubical-set
model). It uses the thirteenth fragment, [bool.horn](../theories/cubical/bool.horn),
which is new in Horn and not a kamo3 snapshot.

Oracles use format 2, which records the theory size they were encoded
against; appending fragments does not change how existing oracles decode.

## Acceptance and trust

The twelve files in [theories/cubical](../theories/cubical) specify contexts,
levels, dependent products, substitution, interval/face operations, restricted
judgments, systems, composition, dependent pairs, equivalences and Glue.
The selected theory contains 351 rules and is explicit application data.
Keeping executable kernel code small does not remove the obligation to audit
these mathematical rules. `src/kernel.rs` has no
special treatment of these symbols and was not changed for this integration.

An oracle is untrusted compressed evidence. `oracle::check` streams its
decoded steps into the existing ground kernel with the fixed, caller-selected
goals. Both decoding and checking must succeed. A hash or successful decoding
alone never establishes acceptance. The same helper is used by `oracle-kernel`
and the bundled CLI. Wrong goals, malformed oracles and unknown examples fail.

This checks derivability from the rules; the cubical rules' mathematical
adequacy and semantic soundness remain separate obligations. The Rust kernel
is not formally verified by the Agda model. A separate bounded
[producer and core source frontend](CUBICAL_PRODUCER.md) now generates fresh
dependent-function/path, face/system, composition and Sigma certificates, with
[certified equivalence definitions](CUBICAL_EQUIVALENCE.md). It also generates [Glue typing and beta/face/eta evidence](CUBICAL_GLUE.md),
but does not yet generate new ua or univalence proofs. The ordinary `.hn` source language and cubical `.hcu`
core source remain separate frontends. See [INTEGRATION.md](INTEGRATION.md) for
how to connect them without expanding the trusted kernel.

## Independent inspection

Export makes a new directory and refuses to overwrite an existing one:

```sh
cargo run --release --locked --offline --bin horn -- cubical export univalence /tmp/horn-univalence
cargo run --release --locked --offline --bin oracle-kernel -- \
  /tmp/horn-univalence/theory.horn /tmp/horn-univalence/goals /tmp/horn-univalence/proof.oracle
cargo run --release --locked --offline --bin horn-oracle -- decode \
  /tmp/horn-univalence/theory.horn /tmp/horn-univalence/goals \
  /tmp/horn-univalence/proof.oracle /tmp/horn-univalence/proof
cargo run --release --locked --offline --bin kernel -- \
  /tmp/horn-univalence/theory.horn /tmp/horn-univalence/goals /tmp/horn-univalence/proof
```

The last two commands materialize the full proof and are optional. Normal
checking streams and does not create the approximately 277 MB original proof.
kamo3's combined generation/checking
unit test exceeded this environment's 8 GiB limit; this is not a fix for the
producer's memory consumption.

## Regeneration inside Horn

`cubical::engine` is kamo3's certificate producer, moved into this
repository (with the bool extension), so every bundled example can be
regenerated without kamo3 or its older pinned kernel:

```sh
cargo run --release --locked --offline --bin horn -- cubical generate canonicity
```

The derivation streams from the producer into the oracle encoder through a
pipe and is never written out; the oracle is then checked as usual. The
engine is untrusted: only the kernel's acceptance counts.

| Example | Time | Peak memory |
| --- | ---: | ---: |
| `ua-transport` | 5 s | 0.1 GB |
| `canonicity` | 185 s | 2.3 GB |
| `univalence` | 60 s | 1.1 GB |

## Provenance and reproduction

The theories and goals are byte-for-byte copies from jihoo12/kamo3 at
`199d67705c591511b0f557b505d2baf019e2687d`, distributed under Apache-2.0,
the same license as Horn. They retain their existing comments. Source-file
SHA-256 hashes, including the upstream compressed proof snapshots, are in
[PROVENANCE.json](../examples/cubical/PROVENANCE.json). The two oracle files
were generated by Horn's encoder and independently checked by its kernel.

A maintainer with an authorized checkout of that exact upstream revision can
reproduce them. Concatenate the theory fragments in `cubical::FRAGMENTS` order,
then, for each NAME (`deep-univalence` and `ua-transport`), run:

```sh
gzip -cd /path/to/kamo3/examples/NAME.proof.gz | \
  target/release/horn-oracle encode THEORY examples/cubical/NAME.goals \
  /dev/stdin examples/cubical/NAME.oracle
target/release/oracle-kernel THEORY examples/cubical/NAME.goals examples/cubical/NAME.oracle
```

Only reproducing the import needs kamo3. The committed data, CLI, decoding,
generic verification and tests are standalone. Fresh path, face/system,
composition and Sigma producers and equivalence-definition lowering are now
implemented in Horn. Fresh equivalence witnesses, Glue-directed composition, ua generation and
migration of the cubical Agda reference remain later steps.
kamo3 should not yet be deleted.
