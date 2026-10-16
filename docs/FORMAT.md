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

## Streaming API

`replay::check(theory, goals, input, scratch, chunk_bytes)` accepts the same
logical format. The scratch file must be seekable, readable, and writable;
its existing contents are truncated. Callers should supply a private file.
The chunk limit must be positive. It also bounds the buffered source for one
form, including comments and newlines, so it affects accepted input sizes.
This byte limit is not a bound on process RSS, total work, or scratch disk use.
