# Standalone integration validation

## Initial replay increment

Validated 2026-10-18 (Asia/Seoul) on Linux x86_64, with an 8 GiB cgroup
memory limit. Nix 2.20.6, the repository's unchanged flake.lock,
Rust 1.91.1 / Cargo 1.91.0. No Cargo dependencies were added.

## Checks

- `cargo fmt --all -- --check` passed.
- `cargo clippy --locked --offline --all-targets -- -D warnings` passed.
- `cargo test --release --locked --offline`: 62 passed, 0 failed.
- The language suite covers nested forward computation, missing clauses,
  wrong sorts, unbound results, first-match commitment on a diverging clause,
  nullary functions, nonlinear patterns, relational search and induction.
  The pre-existing NatLang Agda export is byte-for-byte unchanged.
- A ground forward-computation certificate also replays through `kernel::Theory`
  directly, without the schematic induction/inversion route.
- The cubical suite checks the actual 185,673-step / two-goal U0 univalence
  certificate and 18,849-step ua-transport computation certificate. Corrupt and
  truncated oracles, the false `U0 : U0` goal, undeclared predicates, unknown
  example names and overwriting an export directory are rejected.
- CLI export produces ordinary theory/goals/oracle files independently
  accepted by the same generic checking API used by `oracle-kernel`.

`src/kernel.rs`, `src/lex.rs`, `src/sexp.rs`, `src/schematic.rs` and the Agda
models are unchanged from baseline `4fafc55`. This increment does not extend
either certificate calculus. Generic pipe/decode/check orchestration was
moved from `oracle-kernel` into `oracle::check` so both CLI routes use it.
The checked-in theory and goals match the import hashes in
`examples/cubical/PROVENANCE.json`.

## One runtime observation

After the release build, this command succeeded without kamo3 or an upstream
download:

```sh
target/release/horn cubical check all
```

```text
ACCEPT (cubical univalence): 2 goals, 185673 proof steps, 35830 oracle bytes
ACCEPT (cubical ua-transport): 1 goals, 18849 proof steps, 4086 oracle bytes
```

A single run through the Nix development-shell launcher took 2.665 seconds;
Linux reported maximum child RSS of 369,888 KiB (approximately 361 MiB).
These are one environment's observations, including launcher overhead, not a
cross-platform benchmark or a guaranteed upper bound. The encoded artifacts
are 35,830 and 4,086 bytes; checking still validates every reconstructed step.

## Initial scope

The initial replay increment did not re-run kamo3's expensive producers or repair their OOM test.
It supplied standalone replay of real evidence, plus bounded execution and
certification of ordinary source-language programs. The fresh producer and
core source increment below now extends that scope. All-level computational
univalence, a total dependent programming fragment and a native compiler
remain on the integration roadmap.
The import preserves the chosen mathematical specification; it does not prove
its semantic soundness. No new Agda soundness theorem is claimed here.


## Fresh generation increment

Validated 2026-10-18 (Asia/Seoul), with the same pinned Nix environment.

- `cargo test --release --locked --offline`: **73 passed, 0 failed**.
- `cargo fmt --all -- --check` and
  `cargo clippy --locked --offline --all-targets -- -D warnings` passed.
- Seven producer tests cover fresh universe-level identities, applications,
  beta/path computation, endpoint rules, mixed binder substitution and
  dimension-dependent contexts. Generation is followed by independent ground
  kernel replay. Forged goals and invented rules are rejected.
- Four source/CLI tests cover fresh inputs, malformed syntax, source bounds,
  false typing/equality goals, rule injection, duplicate names, non-overwriting
  export and independent `kernel` CLI replay. No snapshot is used for these
  fresh certificates.
- The complete suite still checks the bundled univalence and ua-transport
  oracles, ordinary language execution, induction and negative kernel cases.
- `kernel.rs`, `lex.rs`, `sexp.rs`, `schematic.rs`, the object theories and Agda
  models are byte-for-byte unchanged from `3e363a7`. No new Cargo dependencies.

The new release commands produced:

```text
horn cubical run examples/cubical/source/basics.hcu
ACCEPT (generated cubical): 9 goals, 75 proof steps

horn cubical run examples/cubical/source/binders.hcu
ACCEPT (generated cubical): 3 goals, 139 proof steps
```

Fresh generation uses the existing scoped-path theory only. The `.hcu` core
uses explicit annotations and separate de Bruijn namespaces; it has bounded
root reduction and syntactic type matching, not general conversion or the
final named-binder surface syntax. Face/composition/Glue/univalence generation,
the semantic soundness of the theory and source elaboration correctness remain
separate obligations. This does not claim to fix kamo3's large-producer OOM.

## Named binders and certified type conversion

Validated 2026-10-18 (Asia/Seoul) in the same pinned development environment.

- `cargo test --release --locked --offline`: **81 passed, 0 failed**.
- Formatting and `cargo clippy --locked --offline --all-targets -- -D warnings`
  passed.
- Named and explicitly indexed forms produce exactly the same fixed goals
  and evidence. Tests cover local shadowing, anonymous/named binder mixing,
  independent namespaces, binding-site context dependencies, duplicate scope
  names and out-of-scope references.
- Type-conversion tests independently replay explicit `type.conv` evidence
  for reducible expected/inferred types and function/path/universe heads.
  They reject corrupted goals, removed conversion steps, false types,
  universe cumulativity and unsupported equality transport. Both annotated
  operands are checked even when their erased terms are identical.
- No checker, object-theory, Agda model, dependency or flake pin changes were
  needed. This remains untrusted generation of evidence for the existing rules.

Actual release CLI runs and independent replay:

```text
horn cubical run examples/cubical/source/named.hcu
ACCEPT (generated cubical): 6 goals, 148 proof steps

horn cubical run examples/cubical/source/conversion.hcu --emit NEW_DIR
ACCEPT (generated cubical): 9 goals, 234 proof steps

kernel NEW_DIR/theory.horn NEW_DIR/goals NEW_DIR/proof
ACCEPT: 9 goals, 234 proof steps, 19677 bytes, 286 distinct terms
```

Conversion is bounded root beta/path computation in a common universe, not
full normalization under binders/constructors. The path fragment has no general
`eq.conv`; non-reflexive reductions whose equality type would need transport
are reported as unsupported before an invalid transitivity step is emitted.
Nested conversion obligations are bounded at 32. Source/semantic soundness and
the later face/system/composition/Glue migration remain separate work.

## Fresh face and coherent-system evidence

Validated 2026-10-18 (Asia/Seoul), using the same pinned Nix environment.

- `cargo test --release --locked --offline`: **90 passed, 0 failed**.
- Formatting and all-target clippy with `-D warnings` passed.
- Face search agrees with an independent model on 160 generated implications
  over two dimensions and all nine partial assignments. The generic dimension
  case rejects Boolean endpoint excluded middle. Every accepted implication
  is also independently replayed by the generic kernel.
- Compound interval boundaries/local equalities are certified. Unknown or
  out-of-scope faces and interval dimensions are rejected even on false bases.
- System tests cover branch typing, all pairwise overlaps, explicit coverage,
  partial and empty systems, restricted endpoint equalities, full-system
  reduction and all four system shift/substitution operations. Compound
  interval substitution also certifies its effect on face syntax.
- A three-branch case catches non-adjacent overlap inconsistency. A forged
  `rhas.export` from a partial result is rejected by the kernel. False faces
  do not bypass the producer's supported typing/scope checks.
- CLI export includes the actual profile's theory, and the independent kernel
  CLI accepts the exported goals/proof. Composition and Glue rules are not
  present in the systems profile.
- Kernel/lexer/parser/schematic checker, all object-theory files, Agda models,
  Cargo dependencies and flake pins are unchanged from `46e8ed6`.

Actual release CLI results:

```text
horn cubical run examples/cubical/source/faces.hcu
ACCEPT (generated cubical): 9 goals, 90 proof steps

horn cubical run examples/cubical/source/systems.hcu --emit NEW_DIR
ACCEPT (generated cubical): 7 goals, 240 proof steps

kernel NEW_DIR/theory.horn NEW_DIR/goals NEW_DIR/proof
ACCEPT: 7 goals, 240 proof steps, 20311 bytes, 313 distinct terms
```

Theory selection is explicit in `Generated.profile` and `Generated.theory`:
path-only requests use one existing fragment; face assertions use two;
system/restricted assertions use the first five existing fragments. The
certificate cannot introduce rules. Local search and restricted inference are
bounded subsets, not complete decision procedures. The new producer does not
yet construct composition, Glue or univalence proofs, and no semantic/model
soundness theorem is claimed for the source frontend or imported specification.

## Native restricted typing and composition

Validated implementation commits `b157480` and `1948b94` in the same rootless
Nix development shell (Rust 1.91.1). These increments add untrusted proof
search only; no kamo3 process or frozen oracle is used to generate fresh
`.hcu` evidence.

- `cargo test --release --locked --offline`: **98 passed, 0 failed**.
- `cargo fmt --all -- --check` and
  `cargo clippy --release --locked --offline --all-targets -- -D warnings` pass.
- Native face-restricted inference checks locally well-formed contexts,
  functions, paths, systems and type/equality conversion. Tests reject casts
  escaping their face, casts using an unrelated dimension, universe
  cumulativity and ill-typed/free terms even on false faces. Ordinary path-only
  requests retain their original profile and conversion limits.
- Composition certifies the family, partial tube, both endpoint types, base
  and start compatibility. Active-face computation requires an explicit face
  implication and a typed one-endpoint tube. Tests reject bad tube/base types,
  inconsistent starts, insufficient tube coverage, free variables/dimensions,
  binder escape and unsupported empty-face/global computation.
- Tests independently replay all four composition shifts/substitutions,
  including an ordinary argument containing a free dimension shifted under
  the composition binder, compound face substitution, and source shadowing.
  Profile selection scans erased annotations and context types too. Forged
  conversion/composition steps are rejected by the generic kernel.
- CLI exports contain the exact selected theory. Both new source files were
  exported and replayed in separate `kernel` processes (results below).
- Existing bundled univalence and ua-transport replay and the ordinary `.hn`
  arithmetic/induction example still pass.
- A direct diff against `120a8d8` confirms no changes to `src/kernel.rs`
  (still 547 lines), lexer/S-expression parser, schematic checker, any theory
  file, Agda models, Cargo dependencies or flake pins. No new kernel rule,
  postulate or univalence primitive was introduced.

Actual CLI results, invoked inside `nix develop`:

```text
horn cubical run examples/cubical/source/restricted.hcu --emit NEW_DIR
ACCEPT (generated cubical): 8 goals, 286 proof steps
kernel NEW_DIR/theory.horn NEW_DIR/goals NEW_DIR/proof
ACCEPT: 8 goals, 286 proof steps, 34649 bytes, 354 distinct terms

horn cubical run examples/cubical/source/composition.hcu --emit OTHER_NEW_DIR
ACCEPT (generated cubical): 8 goals, 683 proof steps
kernel OTHER_NEW_DIR/theory.horn OTHER_NEW_DIR/goals OTHER_NEW_DIR/proof
ACCEPT: 8 goals, 683 proof steps, 79806 bytes, 795 distinct terms

horn cubical check all
ACCEPT (cubical univalence): 2 goals, 185673 proof steps, 35830 oracle bytes
ACCEPT (cubical ua-transport): 1 goals, 18849 proof steps, 4086 oracle bytes

horn examples/lang/program.hn
square (add 2 3) => 25
add (square 3) (mul 2 4) => 17
certificate accepted: 4 goals, 72 steps, 1 inductions
```

The composition profile contains exactly the existing first six fragments;
it does not include Sigma, Glue or type-directed computation extensions.
Composition typing/face computation is not a complete computational
univalence evaluator. General congruence/dependent transport, type-directed
composition, fresh Sigma/equivalence/Glue/ua generation and `.hn`/`.hcu`
frontend integration remain open. Restricted search remains bounded and
incomplete. These tests do not establish semantic adequacy of the cubical
specification or executable-to-Agda refinement.

## Dependent Sigma pairs and equivalence definitions

Validated implementation commits `9449d77` and `921b572` in the rootless Nix
shell (Rust 1.91.1). All fresh generation remains Horn-owned and uses neither
a kamo3 process nor frozen oracle data.

- `cargo test --release --locked --offline`: **108 passed, 0 failed**.
- `cargo fmt --all -- --check` and strict all-target release clippy pass.
- A further targeted check verifies that corrupting a definition fact used
  only in erased metadata is rejected, even when no definition assertion is
  an exported goal. Every emitted step is checked.
- Sigma formation, annotated pairs, dependent first/second projections,
  projection beta and pair eta emit evidence for existing rules. Second
  projection beta retains BODY[fst(pair)] as its natural type; using the
  equation at BODY[FIRST] requires checked conversion. Tests reject bad
  components, annotations, dependencies, mixed-pair eta, unscoped terms and
  face casts escaping globally, and replay all four substitutions.
- `contr`, `fiber`, `isequiv` and `equiv` elaborate to Pi/Sigma/Path terms.
  Every expansion/lift is certified with the existing def.* and transform
  rules. Generic types at differing universe levels, a supplied isEquiv
  witness, function projection and locally well-formed fiber endpoints pass.
- `expand` fixes a definition-expansion goal from the caller's EXPECTED term;
  mismatch, ill-typed arguments/expected annotations, variable capture and
  fake equivalence witnesses are rejected. Independently written named
  expansions exercise ordinary AND dimension lifting under nested binders.
- Input and each intermediate expanded tree are bounded before recursive
  quotation/further duplication. The expanded request must also fit its
  shared node budget. Tests reject nested macro growth and oversized public
  API syntax before inference.
- Profile selection scans contexts and erased annotations. Sigma uses the
  first seven fragments; definitions use the first eight. Neither fresh
  profile includes Glue. Macro syntax never becomes a new object constructor.
- Both actual CLI exports replay in independent generic kernel processes.
  Bundled univalence/ua-transport replay and ordinary arithmetic/induction
  execution also pass, with the unchanged counts below.
- A diff against `2f86b54` confirms no change to the 547-line kernel,
  lexer/S-expression parser, schematic checker, any object theory, Agda
  models, Cargo dependencies or flake pins.

Actual release CLI results, inside `nix develop`:

```text
horn cubical run examples/cubical/source/sigma.hcu --emit NEW_DIR
ACCEPT (generated cubical): 10 goals, 185 proof steps
kernel NEW_DIR/theory.horn NEW_DIR/goals NEW_DIR/proof
ACCEPT: 10 goals, 185 proof steps, 15760 bytes, 230 distinct terms

horn cubical run examples/cubical/source/equivalence.hcu --emit OTHER_NEW_DIR
ACCEPT (generated cubical): 12 goals, 1541 proof steps
kernel OTHER_NEW_DIR/theory.horn OTHER_NEW_DIR/goals OTHER_NEW_DIR/proof
ACCEPT: 12 goals, 1541 proof steps, 341840 bytes, 1683 distinct terms

horn cubical check all
ACCEPT (cubical univalence): 2 goals, 185673 proof steps, 35830 oracle bytes
ACCEPT (cubical ua-transport): 1 goals, 18849 proof steps, 4086 oracle bytes

horn examples/lang/program.hn
square (add 2 3) => 25
add (square 3) (mul 2 4) => 17
certificate accepted: 4 goals, 72 steps, 1 inductions
```

Definition expansion and type formation do not construct an equivalence
witness. The pair example uses an explicitly declared isEquiv witness; it is
not a fresh proof that the identity function is an equivalence. The object
*def predicates describe syntax; source expand checks well-formed arguments
and EXPECTED separately. Stronger congruence/dependent transport,
type-directed composition, fresh equivalence witnesses and Glue/ua/univalence
producers, and connection to the ordinary frontend remain open. No semantic
soundness or executable-to-Agda refinement theorem is claimed here.

## Fresh Glue typing and beta/face/eta evidence

Validated implementation commits `0ac8b0a` and `641e26f` in the rootless Nix
shell (Rust 1.91.1). Fresh evidence is generated in Horn without kamo3 or any
frozen oracle. The existing ninth Glue theory fragment is used unchanged.

- `cargo test --release --locked --offline`: **117 passed, 0 failed**.
- `cargo fmt --all -- --check` and strict all-target release clippy pass.
- Nine Glue regression tests cover formation, value creation, elimination,
  beta, type/value/unglue face equations and reconstruction eta, with separate
  generic-kernel replay. Corrupted typing/face/eta steps are rejected.
- Every value checks its partial value, ambient base, mapped boundary and
  their overlap equality. Wrong equivalences, types, universe levels and
  inconsistent boundaries fail before export. No equivalence axiom or fresh
  witness proof is substituted for an obligation.
- Partially typed system equivalences and contexts well formed only on a face
  work. Covered compound faces compute; unrelated faces and the putative
  endpoint excluded middle do not give global equations. A forged req.export
  from a local Glue equation is rejected by the generic checker.
- All twelve ordinary/dimension operations for glue-type/glue/unglue replay,
  including free ordinary/dimension references and compound interval
  substitution in both the attaching face and a computed equivalence.
- A regression exposed a reducible alias to an active Glue type: normalizing
  past that head lost the structure required by unglue. Restricted exposure
  can now stop at the required Glue head, retaining checked rhas.conv evidence
  at each step. Global and local aliases pass; aliases to Nat still fail.
- Empty-face systems provide scoped typed partial evidence. Existing req.false
  and rhas.conv also legitimately retype already typed terms between
  well-formed types in the same universe on ff. Tests distinguish this valid
  behavior from unscoped/unsupported terms. No rhas.false step is used or added.
- Source/macro/annotation selection picks exactly the first nine fragments.
  The equality/congruence extension and type-directed computation fragments
  are absent. CLI export includes the exact selected theory, not all rules.
- Both actual CLI exports replay in separate kernel processes. Existing
  univalence/ua-transport replay and ordinary arithmetic/induction execution
  retain their previous results.
- A direct diff against `6c829e6` confirms no changes to the 547-line kernel,
  lexer/S-expression parser, schematic checker, any object theory, Agda models,
  Cargo dependencies or flake pins.

Actual release CLI results, inside `nix develop`:

```text
horn cubical run examples/cubical/source/glue.hcu --emit NEW_DIR
ACCEPT (generated cubical): 10 goals, 2005 proof steps
kernel NEW_DIR/theory.horn NEW_DIR/goals NEW_DIR/proof
ACCEPT: 10 goals, 2005 proof steps, 678075 bytes, 2161 distinct terms

horn cubical run examples/cubical/source/glue-faces.hcu --emit OTHER_NEW_DIR
ACCEPT (generated cubical): 6 goals, 5013 proof steps
kernel OTHER_NEW_DIR/theory.horn OTHER_NEW_DIR/goals OTHER_NEW_DIR/proof
ACCEPT: 6 goals, 5013 proof steps, 1798515 bytes, 5448 distinct terms

horn cubical check all
ACCEPT (cubical univalence): 2 goals, 185673 proof steps, 35830 oracle bytes
ACCEPT (cubical ua-transport): 1 goals, 18849 proof steps, 4086 oracle bytes

horn examples/lang/program.hn
square (add 2 3) => 25
add (square 3) (mul 2 4) => 17
certificate accepted: 4 goals, 72 steps, 1 inductions
```

The nonempty examples use declared equivalence hypotheses. The closed empty
example gives only the partial typing needed on ff, not a global equivalence
inhabitant. General congruence/dependent transport, type-directed composition
including Glue, fresh equivalence witnesses and ua/univalence generation,
and the connection to the ordinary language frontend remain open. In
particular application does not yet reduce a projected pair underneath its
function head in this profile. This increment is not a full computational
univalence implementation. Object-theory adequacy, source elaboration
correctness and executable-to-Agda refinement remain separate obligations.
