use horn::{
    cubical::{
        producer::{self, Profile},
        source,
    },
    kernel::Theory,
};

fn replay(src: &str) -> producer::Generated {
    let out = source::run(src).unwrap();
    assert_eq!(out.profile, Profile::Equivalence);
    Theory::parse(&out.theory)
        .unwrap()
        .check(&out.goals, &out.proof)
        .unwrap();
    out
}

#[test]
fn definitions_expand_with_certificates_and_form_usable_types() {
    let out = replay(include_str!("../examples/cubical/source/equivalence.hcu"));
    assert_eq!(out.checked.goals, 12);
    for rule in [
        "def.contr",
        "def.fiber",
        "def.isequiv",
        "def.equiv",
        "rhas.sigma",
        "rhas.pair",
        "rhas.fst",
        "rhas.conv",
    ] {
        assert!(out.proof.contains(rule), "missing {rule}");
    }
    assert!(out.goals.contains("(equivdef nat nat (sigma"));
    assert!(!out.goals.contains("(equiv nat"));
    let corrupt = out.proof.replace("def.equiv", "def.contr");
    assert!(
        Theory::parse(&out.theory)
            .unwrap()
            .check(&out.goals, &corrupt)
            .is_err()
    );
}

#[test]
fn expansion_goals_are_fixed_and_invalid_types_do_not_become_equivalences() {
    for src in [
        "(expand bad (contr nat) nat)",
        "(expand bad (fiber nat nat (lam x nat x) zero) (sigma a nat (path nat (app (lam x zero x) a) zero)))",
        "(expand bad (equiv nat nat) (sigma nat nat))",
        "(expand bad (contr zero) (sigma c zero (pi x zero (path zero c x))))",
        "(expand bad (fiber nat nat zero zero) (sigma a nat (path nat (app zero a) zero)))",
        "(expand bad (equiv (v 0) nat) nat)",
        "(check bad (equiv zero nat) (u 0))",
        "(check bad (fiber nat nat (lam x nat x) nat) (u 0))",
        "(check bad (isequiv nat nat zero) (u 0))",
        "(check bad (lam x nat x) (equiv nat nat))",
        "(check bad (pair (equiv nat nat) (lam x nat x) zero) (equiv nat nat))",
        "(check-on bad (scope (i) ((P (path (u 0) nat nat)) (x (papp P i)))) ft (fiber nat nat (lam y nat y) x) (u 0))",
        "(rule bad () (equivdef nat nat nat))",
    ] {
        let err = source::run(src)
            .err()
            .unwrap_or_else(|| panic!("accepted {src}"));
        assert!(!err.contains("generated certificate rejected"), "{err}");
    }
}

#[test]
fn independent_named_expansions_preserve_both_variable_namespaces() {
    let src = "
(expand dimension-fiber (scope (i) ((p (path nat zero zero))))
  (fiber nat nat (lam x nat x) (papp p i))
  (sigma a nat (path nat (app (lam x nat x) a) (papp p i))))
(expand nested-dimensions (scope (i) ((p (path nat zero zero))))
  (contr (fiber nat nat (lam x nat x) (papp p i)))
  (sigma c (fiber nat nat (lam x nat x) (papp p i))
    (pi x (fiber nat nat (lam x nat x) (papp p i))
      (path j (fiber nat nat (lam x nat x) (papp p i)) c x))))
";
    let out = replay(src);
    assert_eq!(out.checked.goals, 2);
    for rule in ["dshift.papp", "shift.papp", "shift.sigma"] {
        assert!(out.proof.contains(rule));
    }
    let captured = src.replace(
        "(path j (fiber nat nat (lam x nat x) (papp p i)) c x)",
        "(path j (fiber nat nat (lam x nat x) (papp p j)) c x)",
    );
    assert!(source::run(&captured).is_err());
}

#[test]
fn expansion_growth_and_public_api_syntax_are_bounded_before_quotation() {
    let nested = format!("{}nat{}", "(contr ".repeat(12), ")".repeat(12));
    let err = source::run(&format!("(check large {nested} (u 0))"))
        .err()
        .unwrap();
    assert!(
        err.contains("10000 nodes") || err.contains("depth 32"),
        "{err}"
    );
    use horn::cubical::{
        ast::{Definition, Term},
        producer::{Judgment, Request},
    };
    let mut term = Term::Nat;
    for _ in 0..40 {
        term = Term::Defined(Box::new(Definition::Contr(term)));
    }
    let request = Request {
        name: "api-bounds".into(),
        dimensions: 0,
        context: vec![],
        judgment: Judgment::Has {
            term,
            ty: Term::Universe(0),
        },
    };
    assert!(producer::produce(&[request]).is_err());
}

#[test]
fn erased_annotations_select_equivalence_without_installing_glue() {
    let out = replay(
        "(check erased (app (lam x (app (lam T (u 1) (u 0)) (equiv (u 0) (u 0))) zero) nat) nat)",
    );
    assert!(!out.goals.contains("(sigma"));
    assert!(out.theory.contains("(pred equivdef"));
    assert!(!out.theory.contains("(ctor glue"));
    // This macro occurs only in erased metadata; its unused definition fact
    // must still be checked, even though the result goal has no macro terms.
    let corrupt = out.proof.replace("def.equiv", "def.contr");
    assert!(
        Theory::parse(&out.theory)
            .unwrap()
            .check(&out.goals, &corrupt)
            .is_err()
    );
    let out = source::run("(check unchanged zero nat)").unwrap();
    assert_eq!(out.profile, Profile::Path);
}

#[test]
fn definitions_export_the_selected_theory_and_replay_in_a_separate_kernel() {
    use std::{fs, process::Command};
    let dir = std::env::temp_dir().join(format!("horn-equiv-export-{}", std::process::id()));
    assert!(!dir.exists());
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/cubical/source/equivalence.hcu");
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
        Profile::Equivalence.theory()
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
