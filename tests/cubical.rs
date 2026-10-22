//! The cubical package runs from this repository's data. Neither a kamo3
//! checkout nor a theory-specific extension to the kernel is involved.
use horn::{cubical, oracle};
use std::{fs, process::Command};

#[test]
fn real_univalence_and_transport_certificates_check() {
    let theory = cubical::theory();
    for (example, goals, steps) in [
        (&cubical::EXAMPLES[0], 2, 185_673),
        (&cubical::EXAMPLES[1], 1, 18_849),
        (&cubical::EXAMPLES[2], 3, 231_279),
    ] {
        let report = oracle::check(&theory, example.goals, example.oracle).unwrap();
        assert_eq!((report.goals, report.steps), (goals, steps));
    }
}

#[test]
fn transport_along_ua_of_not_computes_to_the_other_boolean() {
    let example = cubical::EXAMPLES
        .iter()
        .find(|e| e.name == "canonicity")
        .unwrap();
    let goals: Vec<_> = example.goals.lines().collect();
    assert_eq!(goals.len(), 3);
    assert!(goals[0].starts_with("(goal not-is-an-equivalence (rhas z nil ft (pair"));
    // Closed judgments in the empty context, ending in a boolean literal.
    assert!(
        goals[1].starts_with("(goal transport-ua-not-true (req z nil ft (comp (glue-type bool")
    );
    assert!(goals[1].ends_with(" ff zero btrue) bfalse bool))"));
    assert!(goals[2].ends_with(" ff zero bfalse) btrue bool))"));
    let theory = cubical::theory();
    for (from, to) in [
        (
            " ff zero btrue) bfalse bool))",
            " ff zero btrue) btrue bool))",
        ),
        (
            " ff zero bfalse) btrue bool))",
            " ff zero bfalse) bfalse bool))",
        ),
    ] {
        let forged = example.goals.replace(from, to);
        assert_ne!(forged, example.goals);
        assert!(oracle::check(&theory, &forged, example.oracle).is_err());
    }
    // Without the bool fragment the certificate has no meaning.
    let without_bool: String = cubical::FRAGMENTS
        .iter()
        .filter(|(name, _)| *name != "bool")
        .map(|(_, source)| format!("{source}\n"))
        .collect();
    assert!(oracle::check(&without_bool, example.goals, example.oracle).is_err());
}

#[test]
fn corrupted_oracles_and_false_goals_are_rejected() {
    let example = &cubical::EXAMPLES[1];
    let theory = cubical::theory();
    let mut corrupt = example.oracle.to_vec();
    corrupt[0] ^= 1;
    assert!(oracle::check(&theory, example.goals, &corrupt).is_err());
    assert!(oracle::check(&theory, example.goals, &example.oracle[..12]).is_err());
    // U0 : U0 is not a consequence of the selected predicative hierarchy.
    assert!(
        oracle::check(
            &theory,
            "(goal forged (has z nil (univ z) (univ z)))",
            example.oracle
        )
        .is_err()
    );
    assert!(oracle::check(&theory, "(goal undeclared (invented))", example.oracle).is_err());
}

#[test]
fn the_cli_exports_independently_checkable_data_without_overwriting() {
    let bin = env!("CARGO_BIN_EXE_horn");
    let list = Command::new(bin)
        .args(["cubical", "list"])
        .output()
        .unwrap();
    assert!(list.status.success());
    assert!(String::from_utf8_lossy(&list.stdout).contains("ua-transport"));
    let dir = std::env::temp_dir().join(format!("horn-cubical-export-{}", std::process::id()));
    // A stale directory is an error rather than an excuse to remove user data.
    assert!(
        !dir.exists(),
        "temporary path already exists: {}",
        dir.display()
    );
    let export = Command::new(bin)
        .args(["cubical", "export", "ua-transport"])
        .arg(&dir)
        .output()
        .unwrap();
    assert!(
        export.status.success(),
        "{}",
        String::from_utf8_lossy(&export.stderr)
    );
    let theory = fs::read_to_string(dir.join("theory.horn")).unwrap();
    let goals = fs::read_to_string(dir.join("goals")).unwrap();
    let proof = fs::read(dir.join("proof.oracle")).unwrap();
    let report = oracle::check(&theory, &goals, &proof).unwrap();
    assert_eq!((report.goals, report.steps), (1, 18_849));
    let again = Command::new(bin)
        .args(["cubical", "export", "ua-transport"])
        .arg(&dir)
        .output()
        .unwrap();
    assert!(!again.status.success());
    assert_eq!(fs::read(dir.join("proof.oracle")).unwrap(), proof);
    fs::remove_dir_all(dir).unwrap();
    let check = Command::new(bin)
        .args(["cubical", "check", "ua-transport"])
        .output()
        .unwrap();
    assert!(
        check.status.success(),
        "{}",
        String::from_utf8_lossy(&check.stderr)
    );
    assert!(
        String::from_utf8_lossy(&check.stdout)
            .contains("ACCEPT (cubical ua-transport): 1 goals, 18849 proof steps")
    );
    assert!(
        !Command::new(bin)
            .args(["cubical", "check", "missing"])
            .output()
            .unwrap()
            .status
            .success()
    );
}

#[test]
fn the_core_theory_drops_the_unrestricted_layer_and_subsumed_rules() {
    let core = cubical::core_theory();
    let full = cubical::theory();
    let count = |t: &str| cubical::generate::rule_count(t);
    // 396 rules from the kamo3 snapshot plus bool and nat, then 31 for the
    // circle, 2 for closed-term weakening and 4 for scoped identities; the
    // core drops 29 unrestricted-layer rules and one subsumed rule.
    assert_eq!((count(&full), count(&core)), (433, 403));
    for form in horn::sexp::parse(&core).unwrap() {
        let text = form.to_string();
        for p in cubical::UNRESTRICTED {
            assert!(!text.contains(&format!("({p} ")), "{text}");
        }
    }
    assert!(!core.contains("(rule req.comp-nat-zero "));
    assert!(core.contains("(rule req.comp-nat "));
    // The core theory is a subset of the bundled one, rule by rule.
    let full_forms: std::collections::HashSet<String> = horn::sexp::parse(&full)
        .unwrap()
        .iter()
        .map(|f| f.to_string())
        .collect();
    for form in horn::sexp::parse(&core).unwrap() {
        assert!(full_forms.contains(&form.to_string()), "{form}");
    }
    horn::kernel::Theory::parse(&core).unwrap();
}

/// Every term former the theory declares, built in or generated by a data
/// declaration.
fn term_formers(theory: &str) -> Vec<String> {
    horn::sexp::parse(theory)
        .unwrap()
        .iter()
        .filter_map(|form| {
            let xs = form.list().ok()?;
            let is_ctor = xs.first()?.atom().ok()? == "ctor";
            (is_ctor && xs.get(3)?.atom().ok()? == "Tm").then(|| xs[1].atom().unwrap().to_owned())
        })
        .collect()
}

#[test]
fn every_term_former_has_scope_and_substitution_rules() {
    // The scoped identities (theories/cubical/scoped.horn) are admissible
    // because scope, shift and substitution are given structurally for
    // every term former; check that none is missing.
    let hit = cubical::script::run(include_str!("../examples/cubical/script/hit.hcs")).unwrap();
    for theory in [cubical::theory(), hit.certified.theory] {
        let rules: std::collections::HashSet<String> = horn::sexp::parse(&theory)
            .unwrap()
            .iter()
            .filter_map(|form| {
                let xs = form.list().ok()?;
                (xs.first()?.atom().ok()? == "rule").then(|| xs[1].atom().unwrap().to_owned())
            })
            .collect();
        let formers = term_formers(&theory);
        assert!(formers.len() >= 30);
        for c in &formers {
            for p in ["scope", "shift", "subst", "dshift", "dsubst"] {
                let named =
                    |r: &String| *r == format!("{p}.{c}") || r.starts_with(&format!("{p}.{c}."));
                assert!(rules.iter().any(named), "no {p} rule for {c}");
            }
        }
    }
}
