# Input format

All inputs use S-expressions. Whitespace separates tokens; `;` starts a comment
through the end of the line. There are no quoted strings or escape sequences.
The parser rejects nesting deeper than its depth-256 recursion limit.

## Theory

```text
(sort SORT)
(ctor CONSTRUCTOR (INPUT_SORTS...) OUTPUT_SORT)
(pred PREDICATE (ARGUMENT_SORTS...))
(rule RULE (PREMISE_JUDGMENTS...) CONCLUSION_JUDGMENT)
```

Sorts must be declared before use. Constructors and predicates used by a rule
must already be declared. Duplicate declarations within each declaration
category are rejected. A nullary constructor is written as an atom, such as
`z`, rather than `(z)`. A constructor with arguments is a list, such as `(s z)`.
A judgment is a list whose head is a declared predicate.

Rule schema variables are atoms beginning with `?`, with at least one character
after the question mark. They are implicitly universally quantified. Each
variable must have a consistent sort throughout a rule. These variables are
for first-order rule matching, not object-language substitution.

```text
(sort Nat)
(ctor z () Nat)
(ctor s (Nat) Nat)
(pred even (Nat))
(rule zero () (even z))
(rule plus-two ((even ?n)) (even (s (s ?n))))
```

Zero-premise rules are assumptions of the selected theory. A certificate cannot
add new rules. Names such as `eq`, `has`, and `subst` carry no native semantics.

## Goals

```text
(goal NAME GROUND_JUDGMENT)
```

At least one goal is required. Goal names must be unique. Ground judgments
contain no schema variables and must satisfy the declared sorts and arities.

## Certificates

```text
(step INDEX RULE (EARLIER_INDICES...) GROUND_JUDGMENT)
(result GOAL_NAME STEP_INDEX)
```

Steps are numbered consecutively from zero. Premise references appear in the
same order as the rule premises and must refer to existing earlier steps.
One consistent assignment to schema variables must match the stated conclusion
and all referenced premises. Matching is structural, with no implicit rewriting
or normalization. All steps are checked, including those unused by results.

Each requested goal needs exactly one result. Results must point to steps that
already exist, and the judgment must equal the requested goal structurally.
Unknown, repeated, missing, and mismatched results are errors. A result may
appear before later proof steps, but those later steps must still be valid.

## Compact certificates

Two further forms let a certificate omit what the checker can reconstruct.
They are conservative: every ordinary certificate keeps its verdict, and the
set of derivable goals is unchanged.

```text
(step INDEX RULE (EARLIER_INDICES...) ITEM...)
(def ?NAME GROUND_TERM)
```

Each `ITEM` after the premise references is either the stated conclusion
judgment (at most one) or a binding `(?VAR GROUND_TERM)` for a variable of the
rule. Bindings must be distinct and well sorted, and premises, bindings and a
stated conclusion must all agree on one assignment. Without a stated
conclusion, the checker builds it by instantiating the rule's conclusion, so
every conclusion variable must be bound by a premise or an explicit binding.
`(step 1 plus-two (0))` is therefore a complete step for `examples/nat.horn`.

`def` names a ground term of any sort. Later ground terms in the same
certificate may write `?NAME` for it; it means exactly the named term. Names
start with `?`, have at least one more character, and cannot be redefined.
Goals cannot use abbreviations. Since ground terms could not previously
contain `?` atoms, no former certificate changes meaning.

`horn-compress THEORY PROOF OUTPUT` rewrites an ordinary certificate into this
form. It drops steps that no result depends on, replaces a step that repeats
an earlier judgment by that step, writes only the bindings premises cannot
determine, and abbreviates repeated compound subterms. It is untrusted: check
its output with `kernel` like any other certificate.

## Streaming API

`Theory::check_reader(goals, input)` reads the certificate incrementally from
any `BufRead`. Memory is proportional to the number of steps and the number of
distinct subterms, independent of the certificate's size in bytes.

`replay::check(theory, goals, input, scratch, chunk_bytes)` is retained for
compatibility. It requires a positive chunk limit, truncates the scratch file,
and then calls `check_reader`; the limit no longer bounds form size, and the
returned chunk count is always one.
