# Extraction baseline

Source: https://github.com/jihoo12/kamo3

Commit: `6a226630910b34ac89dc77f08a22fe956340aecf`

Date of extraction: 2026-10-16.

At the extraction commit `dfdbde5`, copied byte-for-byte:
`src/kernel.rs`, `src/sexp.rs`, `src/replay.rs`,
and `src/lib.rs`. The two CLI files and `tests/replay.rs` were copied with
the crate name and scratch-file prefix changed from `kamo3` to `horn`.
Generic kernel/parser and CLI tests and the natural-number example were added
for independent use. The LICENSE already present in Horn is retained.

SHA-256 of the core files at extraction (later changes need not match):

```text
5a6a9a0aed8396dbc3b8c1ddbe73e13907ed5475afa59cd618719a4d4760e7eb  src/kernel.rs
d7422855011c8354897411fa3570d04c9d5d68e89f19c1f0c99f3a5b02673acb  src/sexp.rs
994b6fcc3b06fc645993726291df3ba17e342b0f3c188b76820c3a34ade490ab  src/replay.rs
```

The source project contains a Cubical Agda attribution notice. No Agda code,
Cubical library code, cubical theory fragments, or cubical certificate producers
are included in this extraction.

The kamo3 repository remains an application/research repository. Its existing
embedded checker is not changed by this extraction. A future migration should
pin a reviewed Horn commit and run certificate compatibility checks before
removing the embedded copy. Until then, do not assume kamo3 automatically uses
new Horn changes.

Upstream research context:

- [Architecture and status](https://github.com/jihoo12/kamo3/blob/6a226630910b34ac89dc77f08a22fe956340aecf/README.md)
- [Trust notes](https://github.com/jihoo12/kamo3/blob/6a226630910b34ac89dc77f08a22fe956340aecf/TRUST.md)
- [Research plan](https://github.com/jihoo12/kamo3/blob/6a226630910b34ac89dc77f08a22fe956340aecf/RESEARCH_PLAN.md)
