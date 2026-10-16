use horn::{kernel::Theory, replay};
use std::{
    fs::{self, OpenOptions},
    io::{Cursor, Write},
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
const THEORY: &str = "(sort N) (ctor z () N) (ctor s (N) N) (pred p (N)) (pred q (N)) (rule seed () (p z)) (rule qseed () (q z)) (rule inc ((p ?x)) (p (s ?x)))";
const PROOF: &str = "(step 0 seed () (p z))\n(step 1 inc (0) (p (s z)))\n(step 2 inc (1) (p (s (s z))))\n(result g 2)\n";
const GOAL: &str = "(goal g (p (s (s z))))";
fn streamed(
    theory: &str,
    goals: &str,
    proof: &str,
    limit: usize,
) -> Result<(usize, usize, usize), String> {
    let path = std::env::temp_dir().join(format!(
        "horn-replay-test-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let mut file = OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .open(&path)
        .unwrap();
    file.write_all(b"(p (s (s z)))").unwrap(); // Existing scratch data is never an admission.
    let result = replay::check(theory, goals, Cursor::new(proof), &mut file, limit)
        .map(|(r, c)| (r.steps, r.goals, c));
    drop(file);
    fs::remove_file(path).unwrap();
    result
}
#[test]
fn every_chunk_limit_checks_the_same_fixed_goal() {
    let normal = Theory::parse(THEORY).unwrap().check(GOAL, PROOF).unwrap();
    for limit in [1, 40, 64, 128, 4096] {
        let (steps, goals, chunks) = streamed(THEORY, GOAL, PROOF, limit).unwrap();
        assert_eq!((steps, goals, chunks), (normal.steps, normal.goals, 1));
    }
}
#[test]
fn bad_dependencies_rules_sorts_and_ground_instances_are_rejected() {
    let cases = [
        PROOF.replace("step 0", "step 1"),
        PROOF.replace("inc (0)", "inc (2)"),
        PROOF.replace("inc (0)", "inc (1)"),
        PROOF.replace("(step 1 inc (0) (p (s z)))", "(step 1 qseed () (q z))"),
        PROOF.replace("(p (s (s z)))", "(p z)"),
        PROOF.replace("(p z)", "(p ?x)"),
        PROOF.replace("(p z)", "(p (p z))"),
        PROOF.replace("seed ()", "unproved ()"),
        PROOF.replace("inc (1)", "replay-verified-0 ()"),
        "(result g 0)\n(step 0 seed () (p z))".into(),
    ];
    let theory = Theory::parse(THEORY).unwrap();
    for p in cases {
        assert!(theory.check(GOAL, &p).is_err(), "bad fixture {p}");
        for limit in [64, 4096] {
            assert!(streamed(THEORY, GOAL, &p, limit).is_err(), "accepted {p}");
        }
    }
}
#[test]
fn all_results_and_even_unused_steps_must_be_checked() {
    for proof in [
        PROOF.replace("(result g 2)", ""),
        format!("{PROOF}(result g 2)"),
        PROOF.replace("result g", "result unknown"),
        format!("{PROOF}(step 3 inc (0) (p z))"),
        PROOF.replace("result g 2", "result g 3"),
    ] {
        for limit in [64, 4096] {
            assert!(streamed(THEORY, GOAL, &proof, limit).is_err());
        }
    }
    assert!(streamed(THEORY, "(goal g (q z))", PROOF, 64).is_err());
}
#[test]
fn imported_rule_names_cannot_be_called_by_the_input_proof() {
    let proof = "(step 0 seed () (p z))\n(step 1 replay-verified-0 () (p z))\n(result g 1)";
    assert!(streamed(THEORY, "(goal g (p z))", proof, 40).is_err());
    let theory = format!("{THEORY} (rule replay-verified-0 () (q z))");
    streamed(&theory, GOAL, PROOF, 40).unwrap();
    streamed(
        &theory,
        "(goal g (q z))",
        "(step 0 replay-verified-0 () (q z))\n(result g 0)",
        64,
    )
    .unwrap();
}
#[test]
fn multiline_forms_comments_and_invalid_trailing_input_follow_the_core_parser() {
    let p = PROOF.replace("(p (s z))", "(p\n ; middle comment\n (s z))");
    streamed(THEORY, GOAL, &p, 128).unwrap();
    for p in [
        format!("{PROOF}("),
        format!("{PROOF})"),
        format!("{PROOF}(rule fake () (p z))"),
        format!("{PROOF}()"),
    ] {
        assert!(streamed(THEORY, GOAL, &p, 64).is_err());
    }
    assert!(streamed(THEORY, GOAL, PROOF, 0).is_err());
}
