//! Implicational goals, rule hypotheses, application, induction with
//! generalized induction hypotheses, and inversion.
use horn::schematic::check;

const LE: &str = include_str!("../examples/le.horn");
const GOALS: &str = include_str!("../examples/le-trans.goals");
const TRANS: &str = include_str!("../examples/le-trans.proof");

fn rejects(goals: &str, proof: &str, reason: &str) {
    match check(LE, goals, proof.as_bytes()) {
        Ok(_) => panic!("accepted, expected rejection: {reason}"),
        Err(e) => assert!(e.contains(reason), "rejected for another reason: {e}"),
    }
}

#[test]
fn transitivity_by_induction_and_inversion() {
    let r = check(LE, GOALS, TRANS.as_bytes()).unwrap();
    assert_eq!((r.goals, r.inductions, r.inversions), (1, 1, 2));
}

#[test]
fn an_impossible_hypothesis_proves_anything() {
    // No rule concludes le (s A) z, so inversion needs no case.
    let goals = "(var A N) (goal g ((le (s A) z)) (le (s z) z))";
    let proof = "(hyp 0 (le (s A) z)) (invert 1 0 () (le (s z) z) ()) (result g 1)";
    check(LE, goals, proof.as_bytes()).unwrap();
}

#[test]
fn inversion_needs_every_possible_rule() {
    // le A B may come from either rule.
    let goals = "(var A B N) (goal g ((le A (s B))) (le z (s B)))";
    let goals = goals.replace("(var A B N)", "(var A N) (var B N)");
    let proof = "(var M N) (var K N)
        (hyp 0 (le A (s B)))
        (step 1 le.zero () (le z (s B)))
        (invert 2 0 () (le z (s B)) ((le.zero 1 (K))))
        (result g 2)";
    rejects(&goals, proof, "missing case for rule le.succ");
}

#[test]
fn an_inversion_case_must_prove_the_unified_goal() {
    let bad = TRANS.replace(
        "(invert 15 3 (4 5) (le (s P) C) ((le.succ 14 (M Nn))))",
        "(invert 15 3 (4 5) (le P C) ((le.succ 14 (M Nn))))",
    );
    rejects(GOALS, &bad, "proves the wrong judgment");
}

#[test]
fn an_inversion_case_may_not_assume_more() {
    // Case 13 depends on hypothesis 9 (le M2 N2); without it in the
    // context or premises... here we drop hypothesis 6 from the context.
    let bad = TRANS.replace("(invert 14 7 (6 8)", "(invert 14 7 (8)");
    rejects(GOALS, &bad, "uses a hypothesis it may not");
}

#[test]
fn the_unifier_may_not_capture_a_generalized_variable() {
    // Unifying eq X (f B) with eq K K gives X := f B, but hypothesis 1
    // generalizes B: substituting would capture it.
    let theory = "(sort N) (ctor f (N) N) (pred eq (N N)) (rule refl () (eq ?x ?x))";
    let goals = "(var X N) (var B N) (goal g ((eq X (f B))) (eq X X))";
    let proof = "(var K N)
        (hyp 0 (eq X (f B)))
        (hyp 1 () (eq X B) (B))
        (step 2 refl () (eq (f K) (f K)))
        (invert 3 0 (1) (eq X X) ((refl 2 (K))))
        (result g 3)";
    match check(theory, goals, proof.as_bytes()) {
        Ok(_) => panic!("accepted a capturing unifier"),
        Err(e) => assert!(e.contains("capture"), "{e}"),
    }
}

#[test]
fn a_conditional_motive_needs_a_conditional_induction_hypothesis() {
    // Motive le z A ⊢ le A (s (s A)); the successor case may not assume
    // le P (s (s P)) outright.
    let goals = "(var A N) (goal g ((le z A)) (le A (s (s A))))";
    let proof = "(var P N)
        (hyp 0 (le z A))
        (step 1 le.zero () (le z (s (s z))))
        (hyp 2 (le P (s (s P))))
        (step 3 le.succ (2) (le (s P) (s (s (s P)))))
        (induct 4 A (0) (le A (s (s A))) ((1) (3 P)))
        (result g 4)";
    rejects(goals, proof, "not an induction hypothesis");
    // With the rule hypothesis le z P ⊢ le P (s (s P)) it is fine.
    let good = proof
        .replace("(hyp 2 (le P (s (s P))))", "(hyp 2 ((le z P)) (le P (s (s P))) ())")
        .replace("(step 3 le.succ (2) (le (s P) (s (s (s P)))))",
                 "(step 3 le.zero () (le z P)) (apply 4 2 () (3)) (step 5 le.succ (4) (le (s P) (s (s (s P)))))")
        .replace("(induct 4 A (0) (le A (s (s A))) ((1) (3 P)))", "(induct 6 A (0) (le A (s (s A))) ((1) (5 P)))")
        .replace("(result g 4)", "(result g 6)");
    check(LE, goals, good.as_bytes()).unwrap();
}

#[test]
fn application_binds_only_generalized_variables() {
    let bad = TRANS.replace(
        "(apply 12 11 ((B M2) (C N2)) (10 9))",
        "(apply 12 11 ((M M2)) (10 9))",
    );
    rejects(GOALS, &bad, "does not generalize");
}

#[test]
fn a_result_may_use_only_stated_hypotheses() {
    let goals = "(var A N) (var B N) (var C N) (goal trans ((le A B)) (le A C))";
    rejects(goals, TRANS, "depends on hypotheses");
}

#[test]
fn a_proved_implication_applies_as_a_rule() {
    // trans, then le z (s (s z)) from le z (s z) and le (s z) (s (s z)).
    let goals = format!("{GOALS} (goal two (le z (s (s z))))");
    let proof = format!(
        "{TRANS}
        (step 17 le.zero () (le z (s z)))
        (step 18 le.zero () (le z z))
        (step 19 le.succ (18) (le (s z) (s z)))
        (step 20 le.succ (19) (le (s (s z)) (s (s z))))
        (step 21 le.zero () (le z (s z)))
        (step 22 le.succ (21) (le (s z) (s (s z))))
        (apply 23 16 ((A z) (B (s z)) (C (s (s z)))) (17 22))
        (result two 23)"
    );
    check(LE, &goals, proof.as_bytes()).unwrap();
}
