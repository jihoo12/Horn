use horn::{
    cubical::{producer, source},
    kernel::Theory,
};
use std::{fs, process::Command};

const BASICS: &str = include_str!("../examples/cubical/source/basics.hcu");
const BINDERS: &str = include_str!("../examples/cubical/source/binders.hcu");

#[test]
fn source_examples_generate_new_independently_checkable_certificates() {
    for (src, goals) in [(BASICS, 9), (BINDERS, 3)] {
        let out = source::run(src).unwrap();
        assert_eq!(out.checked.goals, goals);
        Theory::parse(producer::THEORY)
            .unwrap()
            .check(&out.goals, &out.proof)
            .unwrap();
    }
    // A previously unseen source assertion is generated without a snapshot.
    let out =
        source::run("(check fresh-higher-identity (lam (u 3) (v 0)) (pi (u 3) (u 3)))").unwrap();
    assert_eq!(out.checked.goals, 1);
}

#[test]
fn source_cannot_add_axioms_rules_or_hide_false_goals() {
    for src in [
        "(rule axiom () (has z nil zero (u z)))",
        "(check bad zero (u 0))",
        "(check self (u 0) (u 0))",
        "(check free (v 0) nat)",
        "(check bad-dim (papp (plam nat zero) (dim 0)) nat)",
        "(equal false zero nat nat)",
        "(check duplicate zero nat) (check duplicate nat (u 0))",
        "(check malformed (lam nat) nat)",
        "(check scope-bad (scope 0 (zero)) zero nat)",
        "(check capture (scope 1 ((path nat zero zero))) (app (lam nat (plam nat (v 0))) (papp (v 0) (dim 0))) (path nat zero zero))",
    ] {
        assert!(source::run(src).is_err(), "accepted {src}");
    }
}

#[test]
fn malformed_syntax_and_resource_limits_are_errors() {
    for src in [
        "",
        "()",
        "(",
        ")",
        "(check)",
        "(check bad (u 33) (u 32))",
        "(check bad (v -1) nat)",
        "(check bad (u 9999999999999999999999999999) nat)",
        "(check bad (scope 33 ()) zero nat)",
        "(check bad (scope 0) zero nat)",
        "(check bad (scope 0 not-a-context) zero nat)",
        "(check bad (papp (plam nat zero) (unknown i0)) nat)",
    ] {
        assert!(source::run(src).is_err(), "accepted {src}");
    }
    assert!(source::run(&" ".repeat((1 << 20) + 1)).is_err());
    assert!(source::run(&"(check x zero nat)".repeat(129)).is_err());
    let nested = format!("{}zero{}", "(lam nat ".repeat(34), ")".repeat(34));
    assert!(source::run(&format!("(check deep {nested} nat)")).is_err());
    let context = "nat ".repeat(33);
    assert!(source::run(&format!("(check wide (scope 0 ({context})) zero nat)")).is_err());
}

#[test]
fn cli_emits_replayable_data_and_rejects_failed_sources_without_export() {
    let bin = env!("CARGO_BIN_EXE_horn");
    let dir = std::env::temp_dir().join(format!("horn-cubical-source-{}", std::process::id()));
    assert!(!dir.exists());
    fs::create_dir(&dir).unwrap();
    let source_path = dir.join("source.hcu");
    let export_dir = dir.join("export");
    fs::write(&source_path, BASICS).unwrap();
    let output = Command::new(bin)
        .args(["cubical", "run"])
        .arg(&source_path)
        .arg("--emit")
        .arg(&export_dir)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("ACCEPT (generated cubical): 9 goals")
    );
    let replay = Command::new(env!("CARGO_BIN_EXE_kernel"))
        .arg(export_dir.join("theory.horn"))
        .arg(export_dir.join("goals"))
        .arg(export_dir.join("proof"))
        .output()
        .unwrap();
    assert!(
        replay.status.success(),
        "{}",
        String::from_utf8_lossy(&replay.stderr)
    );
    let original = fs::read(export_dir.join("proof")).unwrap();
    let overwrite = Command::new(bin)
        .args(["cubical", "run"])
        .arg(&source_path)
        .arg("--emit")
        .arg(&export_dir)
        .output()
        .unwrap();
    assert!(!overwrite.status.success());
    assert_eq!(fs::read(export_dir.join("proof")).unwrap(), original);
    fs::write(&source_path, "(check invalid zero (u 0))").unwrap();
    let rejected_dir = dir.join("rejected");
    let failed = Command::new(bin)
        .args(["cubical", "run"])
        .arg(&source_path)
        .arg("--emit")
        .arg(&rejected_dir)
        .output()
        .unwrap();
    assert!(!failed.status.success());
    assert!(!String::from_utf8_lossy(&failed.stdout).contains("ACCEPT"));
    assert!(!rejected_dir.exists());
    assert!(
        !Command::new(bin)
            .args(["cubical", "run"])
            .arg(&source_path)
            .arg("--typo")
            .output()
            .unwrap()
            .status
            .success()
    );
    fs::remove_dir_all(dir).unwrap();
}
