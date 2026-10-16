use std::process::Command;

#[test]
fn both_clis_accept_the_example_and_reject_wrong_goals_and_usage() {
    let root = env!("CARGO_MANIFEST_DIR");
    for binary in [
        env!("CARGO_BIN_EXE_kernel"),
        env!("CARGO_BIN_EXE_stream-kernel"),
    ] {
        let run = |goals: &str| {
            Command::new(binary)
                .current_dir(root)
                .args(["examples/nat.horn", goals, "examples/nat.proof"])
                .output()
                .unwrap()
        };
        let compact = Command::new(binary)
            .current_dir(root)
            .args([
                "examples/nat.horn",
                "examples/nat.goals",
                "examples/nat.compact.proof",
            ])
            .output()
            .unwrap();
        assert!(compact.stdout.starts_with(b"ACCEPT"));
        let accepted = run("examples/nat.goals");
        assert!(
            accepted.status.success(),
            "{}",
            String::from_utf8_lossy(&accepted.stderr)
        );
        assert!(accepted.stdout.starts_with(b"ACCEPT"));
        let rejected = run("examples/nat.proof");
        assert!(!rejected.status.success());
        assert!(rejected.stderr.starts_with(b"REJECT"));
        let usage = Command::new(binary).output().unwrap();
        assert!(!usage.status.success());
        assert!(String::from_utf8_lossy(&usage.stderr).contains("usage:"));
    }
}

#[test]
fn compressed_certificate_is_accepted() {
    let root = env!("CARGO_MANIFEST_DIR");
    let out = std::env::temp_dir().join(format!("horn-cli-compress-{}", std::process::id()));
    let compress = Command::new(env!("CARGO_BIN_EXE_horn-compress"))
        .current_dir(root)
        .args(["examples/nat.horn", "examples/nat.proof"])
        .arg(&out)
        .output()
        .unwrap();
    assert!(compress.status.success());
    let check = Command::new(env!("CARGO_BIN_EXE_kernel"))
        .current_dir(root)
        .args(["examples/nat.horn", "examples/nat.goals"])
        .arg(&out)
        .output()
        .unwrap();
    let text = std::fs::read_to_string(&out).unwrap();
    std::fs::remove_file(&out).unwrap();
    assert!(check.stdout.starts_with(b"ACCEPT"), "{text}");
    assert!(!text.contains("(even"), "{text}");
}

#[test]
fn oracle_certificate_is_accepted_and_rejected_for_other_goals() {
    let root = env!("CARGO_MANIFEST_DIR");
    let dir = std::env::temp_dir();
    let oracle = dir.join(format!("horn-cli-oracle-{}", std::process::id()));
    let decoded = dir.join(format!("horn-cli-decoded-{}", std::process::id()));
    let encode = Command::new(env!("CARGO_BIN_EXE_horn-oracle"))
        .current_dir(root)
        .args([
            "encode",
            "examples/nat.horn",
            "examples/nat.goals",
            "examples/nat.proof",
        ])
        .arg(&oracle)
        .output()
        .unwrap();
    assert!(
        encode.status.success(),
        "{}",
        String::from_utf8_lossy(&encode.stderr)
    );
    let check = |goals: &str| {
        Command::new(env!("CARGO_BIN_EXE_oracle-kernel"))
            .current_dir(root)
            .args(["examples/nat.horn", goals])
            .arg(&oracle)
            .output()
            .unwrap()
    };
    assert!(
        check("examples/nat.goals")
            .stdout
            .starts_with(b"ACCEPT (oracle)")
    );
    let other = dir.join(format!("horn-cli-goals-{}", std::process::id()));
    std::fs::write(&other, "(goal four-is-even (even (s (s (s z)))))").unwrap();
    let rejected = check(other.to_str().unwrap());
    assert!(rejected.stderr.starts_with(b"REJECT"));
    let decode = Command::new(env!("CARGO_BIN_EXE_horn-oracle"))
        .current_dir(root)
        .args(["decode", "examples/nat.horn", "examples/nat.goals"])
        .args([&oracle, &decoded])
        .output()
        .unwrap();
    assert!(decode.status.success());
    let kernel = Command::new(env!("CARGO_BIN_EXE_kernel"))
        .current_dir(root)
        .args(["examples/nat.horn", "examples/nat.goals"])
        .arg(&decoded)
        .output()
        .unwrap();
    for f in [&oracle, &decoded, &other] {
        std::fs::remove_file(f).unwrap();
    }
    assert!(kernel.stdout.starts_with(b"ACCEPT"));
}
