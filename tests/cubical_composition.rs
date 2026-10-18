use horn::{
    cubical::{
        producer::{self, Profile},
        source,
    },
    kernel::Theory,
};
use std::{fs, process::Command};

fn replay(src: &str) -> producer::Generated {
    let out = source::run(src).unwrap();
    assert_eq!(out.profile, Profile::Composition);
    Theory::parse(&out.theory)
        .unwrap()
        .check(&out.goals, &out.proof)
        .unwrap();
    out
}

#[test]
fn composition_certifies_family_tube_endpoints_and_start_compatibility() {
    let out = replay(include_str!("../examples/cubical/source/composition.hcu"));
    assert_eq!(out.checked.goals, 8);
    for rule in [
        "rhas.comp",
        "req.comp-face",
        "req.conv",
        "req.p0-r",
        "req.p1-r",
        "rhas.system",
    ] {
        assert!(out.proof.contains(rule), "missing {rule}");
    }
    for corrupt in [
        out.proof.replace("rhas.comp", "rhas.global"),
        out.proof.replace("req.comp-face", "req.refl"),
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
fn invalid_tubes_boundaries_scopes_and_unlicensed_computation_are_rejected() {
    for src in [
        "(check bad (comp k nat ft nat zero) nat)",
        "(check bad (comp k nat ft zero nat) nat)",
        "(check bad (scope () ((x nat))) (comp k nat ft x zero) nat)",
        "(check bad (scope (i) ()) (comp k nat ft (system nat (((at0 i) zero))) zero) nat)",
        "(check bad (comp k nat (at0 k) zero zero) nat)",
        "(check bad (comp k nat ft zero (papp (plam j nat zero) k)) nat)",
        "(check bad (comp nat (at0 0) zero zero) nat)",
        "(check bad (comp k nat ff (v 0) zero) nat)",
        "(check bad (comp k nat ff (papp (plam j nat zero) (dim 1)) zero) nat)",
        "(equal bad (comp k nat ff (system nat ()) zero) zero nat)",
        "(equal bad (scope (i) ()) (comp k nat (at0 i) zero zero) zero nat)",
        "(check bad (comp k (u 0) ft nat nat) (u 1))",
    ] {
        let err = source::run(src)
            .err()
            .unwrap_or_else(|| panic!("accepted {src}"));
        assert!(!err.contains("generated certificate rejected"), "{err}");
    }
}

#[test]
fn composition_binders_certify_all_four_substitutions() {
    let src = "
; Ordinary beta substitutes an outer path application through a comp binder.
(equal subst (scope (i) ((p (path nat zero zero))))
  (app (lam x nat (comp k nat ft x x)) (papp p i)) (papp p i) nat)
; Lookup shifts a type containing comp, including its face.
(check shift (scope (i) ((A (comp k (u 1) (for ft (at0 i)) (u 0) (u 0))) (x A))) x A)
; Dimension binder shifts comp within the context and substitutes in the tube.
(check dshift (scope (i) ((A (comp k (u 1) ft (u 0) (u 0))) (x A)))
  (plam j A x) (path j A x x))
; Substitution transforms the OUTER face, not comp's new dimension.
(equal dsubst (scope (i j) ())
  (papp (plam outer nat (comp inner nat (at0 outer) zero zero)) (meet i0 j)) zero nat)
";
    let out = replay(src);
    for rule in [
        "shift.comp",
        "subst.comp",
        "dshift.comp",
        "dsubst.comp",
        "fshift.0",
        "fsubst.0",
        "boundary.meet",
    ] {
        assert!(out.proof.contains(rule), "missing {rule}");
    }
}

#[test]
fn composition_profile_is_selected_even_in_erased_annotations() {
    let out = replay("(check annotation (app (lam x (comp k (u 1) ft (u 0) (u 0)) zero) nat) nat)");
    assert!(!out.goals.contains("(comp"));
    assert!(out.theory.contains("(rule rhas.comp"));
    assert!(!out.theory.contains("(ctor glue"));
    let out = source::run("(check unchanged zero nat)").unwrap();
    assert_eq!(out.profile, Profile::Path);
    assert!(!out.theory.contains("(ctor comp"));
}

#[test]
fn cli_exports_composition_profile_for_independent_kernel_replay() {
    let dir = std::env::temp_dir().join(format!("horn-comp-export-{}", std::process::id()));
    assert!(!dir.exists());
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/cubical/source/composition.hcu");
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
    let theory = fs::read_to_string(dir.join("theory.horn")).unwrap();
    assert_eq!(theory, Profile::Composition.theory());
    let checked = Command::new(env!("CARGO_BIN_EXE_kernel"))
        .arg(dir.join("theory.horn"))
        .arg(dir.join("goals"))
        .arg(dir.join("proof"))
        .output()
        .unwrap();
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stderr)
    );
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn named_comp_binds_only_family_and_tube_even_when_shadowing() {
    use horn::cubical::{
        ast::{Face, Interval, Term},
        producer::Judgment,
    };
    let parsed = source::parse("(check shadow (scope (i j) ((P (path nat zero zero)))) (comp i nat (at0 i) (papp P i) (papp P j)) nat)").unwrap();
    let Judgment::Has {
        term: Term::Comp(_, face, tube, base),
        ..
    } = &parsed[0].judgment
    else {
        panic!("expected comp")
    };
    assert_eq!(*face, Face::End(1, false));
    assert!(matches!(tube.as_ref(), Term::PathApp(_, Interval::Var(0))));
    assert!(matches!(base.as_ref(), Term::PathApp(_, Interval::Var(0))));
    // The same numeric index denotes the newly bound i in tube, and outer j in base.
    assert!(source::run("(check bad (comp k nat (at0 k) zero zero) nat)").is_err());
}
