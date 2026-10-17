use horn::schematic::check;

const NAT: &str = "
(sort N)
(ctor z () N)
(ctor s (N) N)
(pred max (N N N))
(rule max.z () (max z ?n ?n))
(rule max.sz () (max (s ?n) z (s ?n)))
(rule max.ss ((max ?m ?n ?k)) (max (s ?m) (s ?n) (s ?k)))
";

const GOALS: &str =
    "(var L N) (goal idem (max L L L)) (goal two (max (s (s z)) (s (s z)) (s (s z))))";

/// `max l l l` is admissible, not derivable: it needs induction on l.
const IDEM: &str = "
(var P N)
(step 0 max.z () (?n z))
(hyp 1 (max P P P))
(step 2 max.ss (1))
(induct 3 L (max L L L) ((0) (2 P)))
(result idem 3)
(result two (3 (L (s (s z)))))
";

fn rejects(theory: &str, goals: &str, proof: &str, reason: &str) {
    match check(theory, goals, proof.as_bytes()) {
        Ok(_) => panic!("accepted, expected rejection: {reason}"),
        Err(e) => assert!(e.contains(reason), "rejected for another reason: {e}"),
    }
}

#[test]
fn induction_proves_an_admissible_rule() {
    let r = check(NAT, GOALS, IDEM.as_bytes()).unwrap();
    assert_eq!(
        (r.goals, r.open_goals, r.inductions, r.instances),
        (2, 1, 1, 0)
    );
}

#[test]
fn induction_rejects_a_case_for_the_wrong_constructor() {
    let bad = IDEM.replace("((0) (2 P))", "((0) (0 P))");
    rejects(NAT, GOALS, &bad, "proves the wrong judgment");
    let bad = IDEM.replace("((0) (2 P))", "((2 P) (0))");
    rejects(NAT, GOALS, &bad, "case variables do not match");
}

#[test]
fn induction_rejects_a_case_proving_another_judgment() {
    let bad = IDEM.replace("(step 0 max.z () (?n z))", "(step 0 max.z () (?n (s z)))");
    rejects(NAT, GOALS, &bad, "proves the wrong judgment");
}

#[test]
fn induction_rejects_a_hypothesis_that_is_not_the_inductive_one() {
    // Assuming the conclusion itself is circular.
    let bad = "
(var P N)
(step 0 max.z () (?n z))
(hyp 1 (max (s P) (s P) (s P)))
(induct 2 L (max L L L) ((0) (1 P)))
(result idem 2)
(result two (2 (L (s (s z)))))
";
    rejects(NAT, GOALS, bad, "not an induction hypothesis");
}

#[test]
fn induction_rejects_a_case_variable_of_the_judgment() {
    let goals = "(var L N) (var P N) (goal g (max L P P))";
    let bad = "
(step 0 max.z () (?n P))
(hyp 1 (max P P P))
(step 2 max.ss (1))
(induct 3 L (max L P P) ((0) (2 P)))
(result g 3)
";
    rejects(NAT, goals, bad, "invalid case variable");
}

#[test]
fn results_and_instances_cannot_depend_on_hypotheses() {
    let bad = "(hyp 0 (max L L L)) (result idem 0)";
    rejects(NAT, GOALS, bad, "depends on hypotheses");
    let bad = "(hyp 0 (max L L L)) (step 1 max.ss ((0 (L z))))";
    rejects(NAT, GOALS, bad, "which has hypotheses");
}

#[test]
fn instances_substitute_only_well_sorted_terms() {
    let theory = format!("{NAT} (sort B) (ctor t () B)");
    let bad = IDEM.replace("(3 (L (s (s z))))", "(3 (L t))");
    rejects(&theory, GOALS, &bad, "ill-sorted term");
}

#[test]
fn a_free_premise_variable_of_an_empty_sort_is_rejected() {
    // E has no constructors, so `q` is not derivable: a derivation of
    // `(p X)` for a variable X of sort E has no ground instance.
    let theory = "
(sort E)
(pred p (E))
(pred q ())
(rule intro () (p ?x))
(rule elim ((p ?x)) (q))
";
    let proof = "(var X E) (step 0 intro () (p X)) (step 1 elim (0)) (result g 1)";
    rejects(theory, "(goal g (q))", proof, "premise variable absent");
}

#[test]
fn ground_certificates_keep_their_verdict() {
    let theory = include_str!("../examples/nat.horn");
    let goals = include_str!("../examples/nat.goals");
    for proof in [
        include_str!("../examples/nat.proof"),
        include_str!("../examples/nat.compact.proof"),
    ] {
        check(theory, goals, proof.as_bytes()).unwrap();
    }
}

#[test]
fn induction_variable_must_occur_in_the_judgment() {
    // S has no ground terms, so `false` has no derivation. If X did not
    // occur in the judgment, the only case could be its own hypothesis.
    let theory = "
(sort S)
(ctor next (S) S)
(pred false ())
";
    let goals = "(var X S) (goal g (false))";
    let bad = "(var Y S) (hyp 0 (false)) (induct 1 X (false) ((0 Y))) (result g 1)";
    rejects(theory, goals, bad, "must occur in the judgment");
}
