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
        assert!(out.proof.contains(&format!(" {rule} (")), "missing {rule}");
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

#[test]
fn partial_equivalences_and_locally_well_formed_contexts_stay_on_their_faces() {
    let src = include_str!("../examples/cubical/source/glue-faces.hcu");
    let out = replay(src);
    assert_eq!(out.checked.goals, 6);
    assert!(out.proof.contains("rhas.system"));
    assert!(out.proof.contains("rctx.cons"));
    assert!(out.proof.contains("rhas.conv"));
    // Existing req.false relates well-formed types on ff; rhas.conv may then
    // retype an already typed term at the same universe. This is valid evidence,
    // not a new false-elimination primitive or an equivalence off the face.
    let empty = replay("(check empty-cast (glue-type nat ff nat zero) (u 0))");
    assert!(empty.proof.contains("req.false"));
    assert!(empty.proof.contains("rhas.conv"));
}

#[test]
fn face_equations_cannot_escape_and_false_faces_do_not_hide_bad_terms() {
    for src in [
        "(equal bad (scope (i) ((e (equiv nat nat)))) (glue-type nat (at0 i) nat e) nat (u 0))",
        "(equal-on bad (scope (i j) ((e (equiv nat nat)))) (at0 j) (glue-type nat (at0 i) nat e) nat (u 0))",
        "(check bad (scope (i) ((e (equiv nat nat)))) (glue (glue-type nat (at0 i) nat e) zero (app (fst e) zero)) nat)",
        "(equal bad (scope (i) ((e (equiv nat nat)) (item (glue-type nat (at0 i) nat e)))) (unglue item) (app (fst e) item) nat)",
        "(check bad (glue-type nat ff nat (v 0)) (u 0))",
        "(check bad (scope () ((item (app (lam T (u 0) T) nat)))) (unglue item) nat)",
        "(equal bad (scope (i) ((e (equiv nat nat)))) (glue-type nat (for (at0 i) (at1 i)) nat e) nat (u 0))",
        "(check bad (glue-type nat (at0 0) nat (system (equiv nat nat) ())) (u 0))",
        "(check bad (glue-type nat ff nat (system (equiv nat nat) ((ff (v 0))))) (u 0))",
        "(check bad (unglue (glue (glue-type nat ff nat (system (equiv nat nat) ())) (v 0) zero)) nat)",
        "(check bad (scope (i) ((e (equiv nat nat)))) (glue (glue-type nat (at0 i) nat (system (equiv nat nat) (((at0 i) e)))) zero (app (fst (system (equiv nat nat) (((at0 i) e)))) zero)) (glue-type nat (at0 i) nat (system (equiv nat nat) (((at0 i) e)))))",
        "(equal bad (scope (i) ((e (equiv nat nat)) (a (glue-type nat (at0 i) nat e)) (b (glue-type nat (at0 i) nat e)))) (glue (glue-type nat (at0 i) nat e) a (unglue b)) a (glue-type nat (at0 i) nat e))",
        "(check unsupported (scope () ((w (isequiv nat nat (lam x nat x))))) (glue (glue-type nat ft nat (pair (equiv nat nat) (lam x nat x) w)) zero zero) (glue-type nat ft nat (pair (equiv nat nat) (lam x nat x) w)))",
    ] {
        let err = source::run(src)
            .err()
            .unwrap_or_else(|| panic!("accepted {src}"));
        assert!(!err.contains("generated certificate rejected"), "{err}");
    }
}

#[test]
fn glue_operations_certify_ordinary_and_dimension_substitution_without_capture() {
    let src = "
(equal ordinary (scope (i) ((e (equiv nat nat)) (p (path nat zero zero))))
  (app (lam x nat (unglue (glue (glue-type nat (at0 i) nat e) x (app (fst e) x)))) (papp p i))
  (app (fst e) (papp p i)) nat)
(check shift (scope (i) ((e (equiv (u 0) (u 0)))
    (x (unglue (glue (glue-type (u 0) (at0 i) (u 0) e) nat (app (fst e) nat))))))
  x (unglue (glue (glue-type (u 0) (at0 i) (u 0) e) nat (app (fst e) nat))))
(check dimension (scope (i) ((e (equiv (u 0) (u 0)))
    (x (unglue (glue (glue-type (u 0) (at0 i) (u 0) e) nat (app (fst e) nat))))))
  (plam j (unglue (glue (glue-type (u 0) (at0 i) (u 0) e) nat (app (fst e) nat))) x)
  (path j (unglue (glue (glue-type (u 0) (at0 i) (u 0) e) nat (app (fst e) nat))) x x))
(equal compound-subst (scope (i j) ((e (equiv nat nat))))
  (papp (plam k nat
    (unglue (glue
      (glue-type nat (at0 k) nat (papp (plam h (equiv nat nat) e) k))
      zero (app (fst (papp (plam h (equiv nat nat) e) k)) zero))))
    (meet i0 j))
  (app (fst (papp (plam h (equiv nat nat) e) (meet i0 j))) zero) nat)
";
    let out = replay(src);
    assert_eq!(out.checked.goals, 4);
    for op in ["shift", "subst", "dshift", "dsubst"] {
        for term in ["glue-type", "glue", "unglue"] {
            assert!(
                out.proof.contains(&format!(" {op}.{term} (")),
                "missing {op}.{term}"
            );
        }
    }
    assert!(out.proof.contains("boundary.meet"));
    assert!(out.proof.contains("fsubst.0"));
}

#[test]
fn unglue_exposes_a_hidden_glue_head_before_reducing_its_active_face() {
    let out = replay(
        "(check hidden (scope () ((e (equiv nat nat)) (item (app (lam T (u 0) T) (glue-type nat ft nat e))))) (unglue item) nat)",
    );
    assert!(out.proof.contains("rhas.conv"));
    assert!(out.proof.contains("rhas.unglue"));
    replay(
        "(check-on hidden-local (scope (i) ((e (equiv nat nat)) (item (app (lam T (u 0) T) (glue-type nat (at0 i) nat e))))) (at0 i) (unglue item) nat)",
    );
}

#[test]
fn glue_profile_sees_erased_annotations_and_macro_arguments() {
    let out = replay(
        "(check erased (scope () ((e (equiv (u 0) (u 0))))) (app (lam x (glue-type (u 0) ft (u 0) e) zero) nat) nat)",
    );
    assert!(!out.goals.contains("(glue"));
    replay(
        "(check macro-argument (scope () ((e (equiv nat nat)))) (equiv (glue-type nat ft nat e) nat) (u 0))",
    );
    let out = source::run("(check unchanged zero nat)").unwrap();
    assert_eq!(out.profile, Profile::Path);
}

#[test]
fn glue_export_replays_in_an_independent_kernel_with_exactly_nine_fragments() {
    use std::{fs, process::Command};
    let dir = std::env::temp_dir().join(format!("horn-glue-export-{}", std::process::id()));
    assert!(!dir.exists());
    let src =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/cubical/source/glue.hcu");
    let out = Command::new(env!("CARGO_BIN_EXE_horn"))
        .args(["cubical", "run"])
        .arg(src)
        .arg("--emit")
        .arg(&dir)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(
        fs::read_to_string(dir.join("theory.horn")).unwrap(),
        Profile::Glue.theory()
    );
    let out = Command::new(env!("CARGO_BIN_EXE_kernel"))
        .arg(dir.join("theory.horn"))
        .arg(dir.join("goals"))
        .arg(dir.join("proof"))
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn forged_export_of_a_local_glue_face_equation_is_rejected() {
    use horn::sexp::{self, call};
    let out = replay(
        "(equal-on partial (scope (i) ((e (equiv nat nat)))) (at0 i) (glue-type nat (at0 i) nat e) nat (u 0))",
    );
    let forms = sexp::parse(&out.goals).unwrap();
    let goal = forms[0].list().unwrap()[2].list().unwrap();
    assert_eq!(goal[0].atom().unwrap(), "req");
    let global = call(
        "eq",
        [
            goal[1].clone(),
            goal[2].clone(),
            goal[4].clone(),
            goal[5].clone(),
            goal[6].clone(),
        ],
    );
    let proof = sexp::parse(&out.proof).unwrap();
    let result = proof.last().unwrap().list().unwrap();
    let id = result[2].atom().unwrap();
    let n = out.checked.steps;
    let mut forged = out
        .proof
        .lines()
        .filter(|l| !l.starts_with("(result "))
        .collect::<Vec<_>>()
        .join("\n");
    forged.push_str(&format!(
        "\n(step {n} req.export ({id}) {global})\n(result forged {n})\n"
    ));
    assert!(
        Theory::parse(&out.theory)
            .unwrap()
            .check(&format!("(goal forged {global})"), &forged)
            .is_err()
    );
}
