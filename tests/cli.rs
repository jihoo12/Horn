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
