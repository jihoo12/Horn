use horn::{
    cubical::{
        producer::{self, Profile},
        source,
    },
    kernel::Theory,
    sexp::{self, call},
};
use std::{fs, process::Command};

fn replay(src: &str) -> producer::Generated {
    let out = source::run(src).unwrap();
    assert_eq!(out.profile, Profile::Systems);
    Theory::parse(&out.theory)
        .unwrap()
        .check(&out.goals, &out.proof)
        .unwrap();
    out
}

#[test]
fn systems_certify_branch_types_all_overlaps_and_coverage() {
    let out = replay(include_str!("../examples/cubical/source/systems.hcu"));
    assert_eq!(out.checked.goals, 7);
    for rule in [
        "coherent.side",
        "overlaps.side",
        "req.pdim",
        "req.system-eq",
        "req.system-branch",
        "ssubst.side",
        "sdsubst.side",
        "fsubst.0",
    ] {
        assert!(out.proof.contains(rule), "missing {rule}");
    }
    let corrupt = out.proof.replace("overlaps.side", "overlaps.nil");
    assert!(
        Theory::parse(&out.theory)
            .unwrap()
            .check(&out.goals, &corrupt)
            .is_err()
    );
    let reversed = "(equal reordered (scope (i) ((p (path nat zero zero)))) (system nat (((at0 i) (papp p i)) (ft zero))) zero nat)";
    let out = replay(reversed);
    assert!(out.proof.contains("branch.there"));
}

#[test]
fn partial_and_empty_systems_cannot_be_exported_as_global_typing() {
    let out = replay("(check-on partial (scope (i) ()) (at0 i) (system nat (((at0 i) zero))) nat)");
    let forms = sexp::parse(&out.goals).unwrap();
    let goal = forms[0].list().unwrap()[2].list().unwrap();
    assert_eq!(goal[0].atom().unwrap(), "rhas");
    let global = call(
        "has",
        [
            goal[1].clone(),
            goal[2].clone(),
            goal[4].clone(),
            goal[5].clone(),
        ],
    );
    let all = sexp::parse(&out.proof).unwrap();
    let result = all.last().unwrap().list().unwrap();
    let id = result[2].atom().unwrap();
    let n = out.checked.steps;
    let mut forged = out
        .proof
        .lines()
        .filter(|l| !l.starts_with("(result "))
        .collect::<Vec<_>>()
        .join("\n");
    forged.push_str(&format!(
        "\n(step {n} rhas.export ({id}) {global})\n(result forged {n})\n"
    ));
    assert!(
        Theory::parse(&out.theory)
            .unwrap()
            .check(&format!("(goal forged {global})"), &forged)
            .is_err()
    );
    replay("(check-on empty ff (system nat ()) nat)");
    assert!(source::run("(check empty (system nat ()) nat)").is_err());
    assert!(source::run("(check excluded-middle (scope (i) ()) (system nat (((at0 i) zero) ((at1 i) zero))) nat)").is_err());
}

#[test]
fn all_four_system_substitutions_respect_ordinary_and_dimension_binders() {
    let src = "
(check lookup (scope () ((A (system (u 1) ((ft (u 0))))) (x A))) x A)
(check shifted (scope (i) ((A (system (u 1) ((ft (u 0)) ((at0 i) (u 0))))) (x A)))
  (plam j A x) (path j A x x))
(equal compound-substitution (scope (k l) ())
  (papp (plam i nat (system nat ((ft zero) ((at0 i) zero)))) (meet k l)) zero nat)
(equal ordinary-substitution (app (lam x nat (system nat ((ft x)))) zero) zero nat)
";
    let out = replay(src);
    for rule in [
        "sshift.side",
        "ssubst.side",
        "sdshift.side",
        "sdsubst.side",
        "fshift.0",
        "fsubst.0",
        "boundary.meet",
    ] {
        assert!(out.proof.contains(rule), "missing {rule}");
    }
}

#[test]
fn disjoint_branches_may_differ_but_inconsistent_overlaps_are_rejected() {
    let src = "(check-on disjoint (scope (i) ((x nat))) (for (at0 i) (at1 i)) (system nat (((at0 i) zero) ((at1 i) x))) nat)";
    let out = replay(src);
    assert!(out.proof.contains("req.false"));
    for bad in [
        "(check bad (scope (i) ((x nat))) (system nat ((ft zero) (ft x))) nat)",
        "(check bad (scope (i) ((x nat))) (system nat ((ft zero) ((at0 i) zero) ((at1 i) x))) nat)",
        "(equal-on bad (scope (i) ((x nat))) (for (at0 i) (at1 i)) (system nat (((at0 i) zero) ((at1 i) x))) zero nat)",
        "(check-on bad ff (system nat ((ff (v 0)))) nat)",
        "(check-on bad ff (system nat ((ff nat))) nat)",
        "(check bad (system nat ((ft zero) ((at0 0) zero))) nat)",
        "(equal-on bad (scope (i) ((p (path nat zero zero)))) ft (papp p i) zero nat)",
    ] {
        let err = source::run(bad)
            .err()
            .unwrap_or_else(|| panic!("accepted {bad}"));
        assert!(!err.contains("generated certificate rejected"), "{err}");
    }
}

#[test]
fn new_profiles_export_the_actual_theory_and_replay_with_the_generic_cli() {
    let dir = std::env::temp_dir().join(format!("horn-system-export-{}", std::process::id()));
    assert!(!dir.exists());
    let file = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/cubical/source/systems.hcu");
    let out = Command::new(env!("CARGO_BIN_EXE_horn"))
        .args(["cubical", "run"])
        .arg(file)
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
    assert!(theory.contains("(rule coherent.side"));
    assert!(!theory.contains("(rule req.comp-glue"));
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
fn oversized_and_malformed_systems_are_rejected_before_generation() {
    let large = "(ft zero) ".repeat(17);
    for src in [
        format!("(check wide (system nat ({large})) nat)"),
        "(check bad (system nat (ft zero)) nat)".into(),
        "(check bad (system nat ((ft))) nat)".into(),
    ] {
        assert!(source::run(&src).is_err());
    }
}
