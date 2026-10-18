use horn::{
    cubical::{
        producer::{self, Profile},
        source,
    },
    kernel::Theory,
};

fn replay(src: &str) -> producer::Generated {
    let out = source::run_with_profile(src, Profile::Equality).unwrap();
    assert_eq!(out.profile, Profile::Equality);
    Theory::parse(&out.theory)
        .unwrap()
        .check(&out.goals, &out.proof)
        .unwrap();
    out
}

#[test]
fn computed_function_projection_path_and_unglue_heads_have_explicit_congruence() {
    let out = replay(include_str!(
        "../examples/cubical/source/congruence-heads.hcu"
    ));
    assert_eq!(out.checked.goals, 8);
    for rule in [
        "req.app-cong",
        "req.fst-cong",
        "req.snd-cong",
        "req.papp-cong",
        "req.unglue-cong",
        "req.conv",
    ] {
        assert!(out.proof.contains(&format!(" {rule} (")), "missing {rule}");
    }
    let corrupt = out.proof.replace("req.app-cong", "req.refl");
    assert!(
        Theory::parse(&out.theory)
            .unwrap()
            .check(&out.goals, &corrupt)
            .is_err()
    );
    assert!(!out.theory.contains("(pred filldef"));
}

#[test]
fn equality_profile_is_opt_in_and_a_smaller_requested_profile_cannot_grow() {
    let src = "(equal projected (app (fst (pair (sigma f (pi nat nat) nat) (lam x nat x) zero)) zero) zero nat)";
    replay(src);
    for profile in [Profile::Path, Profile::Sigma, Profile::Glue] {
        assert!(source::run_with_profile(src, profile).is_err());
    }
    assert!(source::run(src).is_err());
    assert!(Profile::parse("arbitrary-theory").is_err());
    let old = source::run("(check old zero nat)").unwrap();
    assert_eq!(old.profile, Profile::Path);
}

#[test]
fn congruence_still_checks_all_endpoints_dependencies_and_faces() {
    for src in [
        "(equal bad (app (fst (pair (sigma f (pi nat nat) nat) (lam x nat x) zero)) nat) zero nat)",
        "(equal bad (snd (pair (sigma A (u 0) A) nat nat)) zero nat)",
        "(equal bad (scope () ((f (pi nat nat)) (x nat))) (app f x) (app f zero) nat)",
        "(check bad nat (u 1))",
        "(equal-on bad (scope (i) ((p (path nat zero zero)))) ft (papp p i) zero nat)",
        "(check bad (glue-type nat ft nat zero) (u 0))",
        "(check-on bad ff (app (lam x nat x) (v 0)) nat)",
    ] {
        let err = source::run_with_profile(src, Profile::Equality)
            .err()
            .unwrap_or_else(|| panic!("accepted {src}"));
        assert!(!err.contains("generated certificate rejected"), "{err}");
    }
}

#[test]
fn cli_selects_fixed_profiles_and_exports_before_an_independent_replay() {
    use std::{fs, process::Command};
    let dir = std::env::temp_dir().join(format!("horn-equality-export-{}", std::process::id()));
    assert!(!dir.exists());
    fs::create_dir(&dir).unwrap();
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/cubical/source/congruence-heads.hcu");
    for (i, profile_first) in [true, false].into_iter().enumerate() {
        let output = dir.join(i.to_string());
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_horn"));
        cmd.args(["cubical", "run"]).arg(&src);
        if profile_first {
            cmd.args(["--profile", "equality", "--emit"]).arg(&output);
        } else {
            cmd.arg("--emit")
                .arg(&output)
                .args(["--profile", "equality"]);
        }
        let out = cmd.output().unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(
            fs::read_to_string(output.join("theory.horn")).unwrap(),
            Profile::Equality.theory()
        );
        let out = Command::new(env!("CARGO_BIN_EXE_kernel"))
            .arg(output.join("theory.horn"))
            .arg(output.join("goals"))
            .arg(output.join("proof"))
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
    let bad = dir.join("invalid");
    let bad_text = bad.to_str().unwrap();
    for options in [
        vec!["--profile", "unknown", "--emit", bad_text],
        vec!["--emit", bad_text, "--profile", "path"],
        vec![
            "--emit",
            bad_text,
            "--profile",
            "equality",
            "--profile",
            "equality",
        ],
        vec!["--emit", bad_text, "--emit", bad_text],
        vec!["--profile"],
        vec!["--emit"],
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_horn"))
            .args(["cubical", "run"])
            .arg(&src)
            .args(options)
            .output()
            .unwrap();
        assert!(!out.status.success());
        assert!(!bad.exists());
    }
    fs::remove_dir_all(dir).unwrap();
}
