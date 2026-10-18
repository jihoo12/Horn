use horn::{
    cubical::{
        producer::{self, Profile},
        source,
    },
    kernel::Theory,
};

fn replay(src: &str) -> producer::Generated {
    let out = source::run(src).unwrap();
    assert_eq!(out.profile, Profile::Sigma);
    Theory::parse(&out.theory)
        .unwrap()
        .check(&out.goals, &out.proof)
        .unwrap();
    out
}

#[test]
fn dependent_pairs_projection_beta_and_eta_are_certified() {
    let out = replay(include_str!("../examples/cubical/source/sigma.hcu"));
    assert_eq!(out.checked.goals, 10);
    for rule in [
        "rhas.sigma",
        "rhas.pair",
        "rhas.fst",
        "rhas.snd",
        "req.fst-beta",
        "req.snd-beta",
        "req.pair-eta",
        "req.conv",
        "rhas.conv",
    ] {
        assert!(out.proof.contains(rule), "missing {rule}");
    }
    for corrupt in [
        out.proof.replace("req.snd-beta", "req.fst-beta"),
        out.proof.replace("req.pair-eta", "req.refl"),
    ] {
        assert!(
            Theory::parse(&out.theory)
                .unwrap()
                .check(&out.goals, &corrupt)
                .is_err()
        );
    }
}

#[test]
fn sigma_substitution_respects_both_binders_and_erased_pair_annotations() {
    let src = "
(check lookup (scope (i) ((p (sigma A (u 0) A)) (x (fst p)))) x (fst p))
(equal ordinary
  (app (lam x nat (pair (sigma y nat (path nat x x)) x (plam j nat x))) zero)
  (pair (sigma y nat (path nat zero zero)) zero (plam j nat zero))
  (sigma y nat (path nat zero zero)))
(check dimension (scope (i) ((p (sigma nat nat))))
  (plam j (sigma nat nat) p) (path j (sigma nat nat) p p))
(equal path-subst (scope (i j) ())
  (papp (plam k (sigma nat nat) (pair (sigma nat nat) zero zero)) (meet i j))
  (pair (sigma nat nat) zero zero) (sigma nat nat))
";
    let out = replay(src);
    for rule in [
        "shift.sigma",
        "subst.sigma",
        "dshift.sigma",
        "dsubst.sigma",
        "subst.pair",
        "dsubst.pair",
    ] {
        assert!(out.proof.contains(rule), "missing {rule}");
    }
}

#[test]
fn pair_annotations_wrong_dependencies_free_variables_and_false_conversions_fail() {
    for src in [
        "(check bad (pair (sigma nat nat) zero nat) (sigma nat nat))",
        "(check bad (pair (sigma A (u 0) A) nat nat) (sigma A (u 0) A))",
        "(check bad (pair nat zero zero) nat)",
        "(check bad (fst zero) nat)",
        "(check bad (snd (pair (sigma A (u 0) A) nat zero)) (u 0))",
        "(equal bad (scope () ((p (sigma nat nat)) (q (sigma nat nat)))) (pair (sigma nat nat) (fst p) (snd q)) p (sigma nat nat))",
        "(check bad (sigma x nat y) (u 0))",
        "(check bad (scope () ((p (sigma nat nat)) (x (fst p)))) x nat)",
        "(check-on bad ff (pair (sigma nat nat) (v 0) zero) (sigma nat nat))",
        "(check bad (sigma (u 1) (u 0)) (u 1))",
        "(equal bad (pair (sigma nat nat) zero zero) (pair (sigma nat (u 0)) zero zero) (sigma nat nat))",
        "(check-on bad (scope (i) ((P (path (u 0) nat nat)) (x (papp P i)))) ft (pair (sigma nat nat) x zero) (sigma nat nat))",
    ] {
        let err = source::run(src)
            .err()
            .unwrap_or_else(|| panic!("accepted {src}"));
        assert!(!err.contains("generated certificate rejected"), "{err}");
    }
}

#[test]
fn metadata_selects_sigma_and_small_profiles_stay_small() {
    let out = replay(
        "(check erased (app (lam x (sigma nat nat) zero) (pair (sigma nat nat) zero zero)) nat)",
    );
    assert!(!out.goals.contains("(sigma"));
    assert!(out.theory.contains("(rule req.snd-beta"));
    assert!(!out.theory.contains("(pred equivdef"));
    let out = source::run("(check old zero nat)").unwrap();
    assert_eq!(out.profile, Profile::Path);
}
