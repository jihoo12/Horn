use horn::{
    cubical::{producer, source},
    kernel::Theory,
};

#[test]
fn type_conversions_and_reducible_heads_have_checked_evidence() {
    let out = source::run(include_str!("../examples/cubical/source/conversion.hcu")).unwrap();
    assert_eq!(out.checked.goals, 9);
    assert!(out.proof.contains("type.conv"));
    assert!(out.proof.contains("eq.beta"));
    assert!(out.proof.contains("eq.p0"));
    assert!(out.proof.contains("eq.p1"));
    assert!(out.proof.contains("eq.pbeta"));
    let replay = Theory::parse(producer::THEORY)
        .unwrap()
        .check(&out.goals, &out.proof)
        .unwrap();
    assert_eq!(replay.goals, 9);
    let wrong_goal = out.goals.replace("(app (lam (v z)) nat)", "(u z)");
    assert_ne!(wrong_goal, out.goals);
    assert!(
        Theory::parse(producer::THEORY)
            .unwrap()
            .check(&wrong_goal, &out.proof)
            .is_err()
    );
    let missing_conversion = out.proof.replace("type.conv", "type.zero");
    assert!(
        Theory::parse(producer::THEORY)
            .unwrap()
            .check(&out.goals, &missing_conversion)
            .is_err()
    );
}

#[test]
fn convertible_context_domains_can_be_used_in_dependent_functions() {
    let out = source::run(
        "(check id (scope () ((A (app (lam B (u 1) (u 0)) (u 0))))) (lam x A x) (pi x A A))",
    )
    .unwrap();
    assert_eq!(out.checked.goals, 1);
    assert!(out.proof.contains("type.conv"));
}

#[test]
fn conversion_does_not_make_false_types_or_universe_cumulativity_available() {
    for src in [
        "(check bad zero (app (lam A (u 0) (pi nat nat)) nat))",
        "(check bad nat (u 1))",
        "(check bad (u 0) (u 0))",
        "(check bad (scope (i) ((p (path (u 0) nat nat)))) zero (papp p i))",
        "(check bad (scope (i) ((p (path (u 0) nat nat)))) (plam j (papp p j) zero) (path j (papp p j) zero zero))",
        "(equal bad (lam x nat x) (lam A (u 0) A) (pi nat nat))",
    ] {
        let err = source::run(src)
            .err()
            .unwrap_or_else(|| panic!("accepted {src}"));
        assert!(
            !err.contains("generated certificate rejected"),
            "emitted invalid evidence instead of reporting its limit: {err}"
        );
    }
}

#[test]
fn unsupported_equality_transport_reports_a_limit_without_forging_a_step() {
    let src = "(equal needs-eq-conv (app (lam x nat x) zero) zero (app (lam A (u 0) A) nat))";
    let err = source::run(src)
        .err()
        .expect("the small producer has no eq.conv route");
    assert!(
        err.contains("equality reduction at a converted type is not supported"),
        "{err}"
    );
    assert!(!err.contains("generated certificate rejected"));
}
