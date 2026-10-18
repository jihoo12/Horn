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
    ] {
        let report = oracle::check(&theory, example.goals, example.oracle).unwrap();
        assert_eq!((report.goals, report.steps), (goals, steps));
    }
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
