use horn::{
    cubical::{
        producer::{self, Profile},
        source,
    },
    kernel::Theory,
};

fn replay(src: &str) -> producer::Generated {
    let out = source::run(src).unwrap();
    assert_eq!(out.profile, Profile::Glue);
    Theory::parse(&out.theory)
        .unwrap()
        .check(&out.goals, &out.proof)
        .unwrap();
    out
}

#[test]
fn glue_formation_values_faces_beta_and_eta_replay_without_new_rules() {
    let out = replay(include_str!("../examples/cubical/source/glue.hcu"));
    assert_eq!(out.checked.goals, 10);
    for rule in [
        "rhas.glue-type",
        "rhas.glue",
        "rhas.unglue",
        "req.glue-type",
        "req.glue-face",
        "req.unglue-beta",
        "req.unglue-face",
        "req.glue-eta",
        "def.equiv",
    ] {
        assert!(out.proof.contains(rule), "missing {rule}");
    }
    for corrupt in [
        out.proof.replace("rhas.glue-type", "rhas.nat"),
        out.proof.replace("req.glue-face", "req.refl"),
        out.proof.replace("req.glue-eta", "req.refl"),
    ] {
        assert!(
            Theory::parse(&out.theory)
                .unwrap()
                .check(&out.goals, &corrupt)
                .is_err()
        );
    }
    assert_eq!(out.theory, Profile::Glue.theory());
    assert!(!out.theory.contains("(rule req.app-cong"));
    assert!(!out.theory.contains("(rule req.comp-glue"));
}

#[test]
fn glue_checks_the_equivalence_partial_value_and_base_compatibility() {
    for src in [
        "(check bad (glue-type nat ft nat zero) (u 0))",
        "(check bad (scope () ((e (equiv nat nat)))) (glue (glue-type nat ft nat e) zero nat) (glue-type nat ft nat e))",
        "(check bad (scope () ((e (equiv nat nat)))) (glue (glue-type nat ft nat e) zero zero) (glue-type nat ft nat e))",
        "(check bad (scope () ((e (equiv nat nat)))) (glue (glue-type nat ft nat e) nat (app (fst e) zero)) (glue-type nat ft nat e))",
        "(check bad (scope () ((e (equiv nat nat)))) (glue-type nat ft (u 0) e) (u 0))",
        "(check bad (unglue zero) nat)",
        "(check bad (glue nat zero zero) nat)",
    ] {
        let err = source::run(src)
            .err()
            .unwrap_or_else(|| panic!("accepted {src}"));
        assert!(!err.contains("generated certificate rejected"), "{err}");
    }
}
