# Oracle certificates

An oracle certificate records only the decisions a checker cannot make by
itself. Everything else, including every conclusion, every premise reference
and almost every term, is reconstructed. Decoding produces an ordinary compact
certificate, which the unchanged kernel then checks, so oracle certificates
add no trusted code.

The idea is Necula and Rahul's *oracle-based checking* (POPL 2001), applied
here to ground Horn certificates, with tabling and adaptive context modelling.

## Reconstruction

Goals are derived top-down, in the order of the goals file. A subgoal is a
judgment that may still contain logic variables.

1. A ground subgoal that was already derived is reused. This costs nothing.
2. Otherwise the candidates are listed in a fixed order. For a non-ground
   subgoal, they are first the earlier judgments that unify with it, in
   derivation order. Then come the rules whose conclusion unifies with it, in
   theory order. If there is exactly one candidate, it costs nothing.
   Otherwise the oracle names one.
3. For a rule, premises are instantiated and solved. A premise that is
   already ground goes first; otherwise the leftmost remaining premise goes
   first. Solving a premise binds variables shared with the other premises,
   which is how unification recovers what a compact certificate would state
   as a binding.
4. A conclusion still open after all its premises takes witness terms from
   the oracle, one constructor at a time.
5. The step is written out as a compact `step`, its judgment is tabled, and
   its number is returned to the parent.

Each choice among *n* candidates is coded as up to *n − 1* binary questions:
"is it this one?". An LZMA-style adaptive binary range coder codes these
questions. Its context is the parent rule and premise position (or the
predicate, for a goal), whether the subgoal is ground, and the candidate. A
decision that the context predicts well costs a small fraction of a bit.

The encoder runs the same reconstruction and reads each decision off a known
derivation. That derivation may be an ordinary or a compact certificate. Steps
that no goal needs are never visited. Because the encoder and decoder are the
same procedure, they stay in step by construction. Nothing that is decided
depends on hash-table iteration order or on term numbering.

## What it achieves

The table covers kamo3's certificates (the full table is in
[BENCHMARKS.md](BENCHMARKS.md)).

| Certificate | Ordinary | Compact | Oracle | Goals file |
| --- | ---: | ---: | ---: | ---: |
| ua-unglue | 4,067,276,087 | 54,591,519 | 63,890 | 59,673 |
| constant-equiv | 761,517,734 | 24,273,371 | 42,308 | 17,875 |
| compute | 39,657,410 | 3,076,975 | 6,698 | 24,409 |
| ua-beta | 26,107,428 | 1,589,886 | 3,123 | 5,012 |

The 4 GB certificate becomes 64 kB, which is about the size of the statement
it proves. Generic compression does not come close: `xz -9` on the compact
form gives 7.2 MB. The reason is structural. These derivations are mostly
determined by their goals, and almost every reference to an earlier judgment
has only one candidate once unification has fixed the subgoal's ground
arguments.

## Trust

`src/oracle.rs`, `horn-oracle`, and the decoding thread in `oracle-kernel` are
untrusted. A wrong or malicious oracle can only make decoding fail, or produce
a certificate that the kernel then checks like any other. Acceptance by
`oracle-kernel` means the kernel accepted the decoded certificate for the
caller's goals. The trust contract in [TRUST.md](TRUST.md) and the Agda proof
are unaffected.

## Limits

- **Decoding cost.** Decoding time and memory follow the size of the
  reconstructed derivation, not the size of the oracle. A 64 kB oracle
  legitimately expands to 1.1 million steps. Nesting is limited to 65,536
  subgoals or witness levels. Reading more than 8 bytes past the end of the
  oracle is an error. There is no limit on the number of steps.
- **Speed and memory on ua-unglue.** Checking takes 3.5 s and 399 MiB, against
  0.79 s and 66 MiB for the compact certificate. The difference is the
  decoder's unification and its tables.
- **Format stability.** The oracle is defined by the reconstruction algorithm
  and its contexts. An oracle is valid only for the exact theory text and the
  same goals in the same order. Version 1 (`horn-oracle 1` header) is
  experimental. Any change to the procedure needs a new version.
- **Dependence on the theory.** Compression depends on the theory being mostly
  deterministic. A theory whose derivations need many arbitrary witness terms
  compresses less, because witnesses are coded constructor by constructor.
