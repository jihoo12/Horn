use horn::{kernel::Theory, sexp::parse};

const THEORY: &str = include_str!("../examples/nat.horn");
const GOALS: &str = include_str!("../examples/nat.goals");
const PROOF: &str = include_str!("../examples/nat.proof");

#[test]
fn standalone_example_checks() {
    let report = Theory::parse(THEORY).unwrap().check(GOALS, PROOF).unwrap();
    assert_eq!((report.steps, report.goals), (3, 1));
}

#[test]
fn one_assignment_must_match_conclusion_and_every_premise() {
    let source = "(sort N) (ctor z () N) (ctor s (N) N)
        (pred p (N)) (pred q (N)) (pred r (N N))
        (rule p0 () (p z)) (rule q1 () (q (s z)))
        (rule join ((p ?x) (q ?x)) (r ?x ?x))";
    let theory = Theory::parse(source).unwrap();
    // Every judgment is sorted, but the two premises demand different x.
    for conclusion in ["(r z z)", "(r z (s z))", "(r (s z) (s z))"] {
        let proof = format!(
            "(step 0 p0 () (p z)) (step 1 q1 () (q (s z)))
             (step 2 join (0 1) {conclusion}) (result g 2)"
        );
        assert!(
            theory
                .check(&format!("(goal g {conclusion})"), &proof)
                .is_err()
        );
    }
    let valid = source.replace("(q (s z))", "(q z)");
    Theory::parse(&valid)
        .unwrap()
        .check(
            "(goal g (r z z))",
            "(step 0 p0 () (p z)) (step 1 q1 () (q z))
             (step 2 join (0 1) (r z z)) (result g 2)",
        )
        .unwrap();
}

#[test]
fn invalid_steps_cannot_hide_behind_a_valid_result() {
    let theory = Theory::parse(THEORY).unwrap();
    for proof in [
        PROOF.replace("step 1", "step 9"),
        PROOF.replace("plus-two (0)", "plus-two (1)"),
        PROOF.replace("plus-two (0)", "plus-two (2)"),
        PROOF.replace("plus-two (0)", "plus-two ()"),
        PROOF.replace("plus-two (0)", "zero (0)"),
        PROOF.replace("plus-two (0)", "unknown (0)"),
        PROOF.replace(
            "(step 1 plus-two (0) (even (s (s z))))",
            "(step 1 plus-two (0) (even z))",
        ),
        format!("{PROOF}(step 3 zero () (even (s z)))"),
        format!("{PROOF}(rule injected () (even z))"),
    ] {
        assert!(theory.check(GOALS, &proof).is_err(), "accepted {proof}");
    }
}

#[test]
fn results_are_exact_complete_and_unique() {
    let theory = Theory::parse(THEORY).unwrap();
    for proof in [
        PROOF.replace("(result four-is-even 2)", ""),
        format!("{PROOF}(result four-is-even 2)"),
        PROOF.replace("result four-is-even", "result unknown"),
        PROOF.replace("result four-is-even 2", "result four-is-even 0"),
        PROOF.replace("result four-is-even 2", "result four-is-even 3"),
    ] {
        assert!(theory.check(GOALS, &proof).is_err());
    }
    assert!(theory.check("", PROOF).is_err());
    assert!(theory.check(&format!("{GOALS}{GOALS}"), PROOF).is_err());
    assert!(
        theory
            .check(&format!("{GOALS}(goal another (even z))"), PROOF)
            .is_err()
    );
    let proof = format!("{PROOF}(result another 0)");
    assert_eq!(
        theory
            .check(&format!("{GOALS}(goal another (even z))"), &proof)
            .unwrap()
            .goals,
        2
    );
}

#[test]
fn sorts_arities_and_groundness_are_enforced() {
    let theory = Theory::parse(THEORY).unwrap();
    for judgment in [
        "(even ?x)",
        "(even (z))",
        "(even (s))",
        "(even (s z z))",
        "(even z z)",
        "(even missing)",
        "(unknown z)",
        "(even (even z))",
    ] {
        assert!(theory.check(&format!("(goal g {judgment})"), "").is_err());
        assert!(
            theory
                .check(
                    "(goal g (even z))",
                    &format!("(step 0 zero () {judgment}) (result g 0)")
                )
                .is_err()
        );
    }
    assert!(Theory::parse("(sort A) (sort B) (pred p (A B)) (rule bad () (p ?x ?x))").is_err());
    assert!(Theory::parse("(sort A) (pred p (A)) (rule bad () (p ?))").is_err());
}

#[test]
fn invalid_declarations_and_malformed_inputs_are_errors() {
    for source in [
        "(sort A) (sort A)",
        "(ctor x () Missing)",
        "(sort A) (ctor x () A) (ctor x () A)",
        "(sort A) (pred p (A)) (pred p (A))",
        "(pred p ()) (rule r () (p)) (rule r () (p))",
        "(sort ?A)",
        "(unknown A)",
        "()",
    ] {
        assert!(Theory::parse(source).is_err(), "accepted {source}");
    }
    for source in ["(", ")", "(a", "((a)"] {
        assert!(parse(source).is_err());
    }
    let nested = format!("{}x{}", "(".repeat(300), ")".repeat(300));
    assert!(parse(&nested).is_err());
}
