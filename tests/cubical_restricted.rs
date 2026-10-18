use horn::{
    cubical::{producer::Profile, source},
    kernel::Theory,
};

#[test]
fn local_types_contexts_and_function_heads_replay_without_new_rules() {
    let out = source::run(include_str!("../examples/cubical/source/restricted.hcu")).unwrap();
    assert_eq!(out.profile, Profile::Systems);
    assert_eq!(out.checked.goals, 8);
    for rule in [
        "rctx.cons",
        "rhas.v",
        "rhas.conv",
        "rhas.app",
        "rhas.lam",
        "req.beta-typed",
        "req.pdim-r",
        "req.p0-r",
        "req.conv",
        "rhas.path",
        "rhas.plam",
        "rhas.papp",
        "req.pbeta-r",
    ] {
        assert!(out.proof.contains(rule), "missing {rule}");
    }
    Theory::parse(&out.theory)
        .unwrap()
        .check(&out.goals, &out.proof)
        .unwrap();
    let corrupt = out.proof.replace("rhas.conv", "rhas.global");
    assert!(
        Theory::parse(&out.theory)
            .unwrap()
            .check(&out.goals, &corrupt)
            .is_err()
    );
}

#[test]
fn local_conversion_does_not_escape_its_face_or_invent_universe_cumulativity() {
    for src in [
        "(check bad (scope (i) ((P (path (u 0) nat nat)) (x (papp P i)))) x nat)",
        "(check-on bad (scope (i) ((P (path (u 0) nat nat)) (x (papp P i)))) ft x nat)",
        "(check-on bad (scope (i j) ((P (path (u 0) nat nat)) (x (papp P i)))) (at0 j) x nat)",
        "(check-on bad (scope (i) ((P (path (u 1) (u 0) (u 0))) (A (papp P i)) (x A))) ft x A)",
        "(check-on bad (scope (i) ()) (at0 i) nat (u 1))",
        "(check-on bad ff (v 0) nat)",
        "(check-on bad ff nat nat)",
    ] {
        let err = source::run(src)
            .err()
            .unwrap_or_else(|| panic!("accepted {src}"));
        assert!(!err.contains("generated certificate rejected"), "{err}");
    }
}
