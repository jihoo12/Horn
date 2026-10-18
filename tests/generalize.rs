//! The generalization pipeline on a standalone example: a ground proof at
//! level zero becomes a schematic proof for every level, whose instances the
//! ground kernel accepts.
use horn::generalize::generalize;
use horn::kernel::Theory;
use horn::schematic::{check, export_agda, instantiate};

const THEORY: &str = include_str!("../examples/levels.horn");
const GOALS: &str = include_str!("../examples/levels.goals");
const PROOF: &str = include_str!("../examples/levels.proof");

fn emit(theory: &str, goals: &str, proof: &str) -> (String, String, Vec<String>) {
    let (mut g, mut p) = (Vec::new(), Vec::new());
    let (_, emitted) = generalize(
        theory,
        goals,
        proof.as_bytes(),
        &["max:2"],
        Some("u:0"),
        Some((&mut g, &mut p)),
    )
    .unwrap();
    let rigid = emitted.unwrap().rigid_goals;
    (
        String::from_utf8(g).unwrap(),
        String::from_utf8(p).unwrap(),
        rigid,
    )
}

fn ground_instance(theory: &str, goals: &str, proof: &str, level: &str) -> (String, String) {
    let (mut g, mut p) = (Vec::new(), Vec::new());
    let binding = [("L".to_owned(), level.to_owned())];
    instantiate(theory, goals, proof.as_bytes(), &binding, &mut g, &mut p).unwrap();
    (String::from_utf8(g).unwrap(), String::from_utf8(p).unwrap())
}

#[test]
fn a_level_zero_proof_holds_at_every_level() {
    let (goals, proof, rigid) = emit(THEORY, GOALS, PROOF);
    assert!(rigid.is_empty());
    assert!(goals.contains("(type (arrow (u L) (arrow (u L) (u L))) (s L))"));
    let report = check(THEORY, &goals, proof.as_bytes()).unwrap();
    assert_eq!((report.open_goals, report.inductions), (1, 1));
    let theory = Theory::parse(THEORY).unwrap();
    for level in ["z", "(s z)", "(s (s (s z)))"] {
        let (g, p) = ground_instance(THEORY, &goals, &proof, level);
        let expected =
            format!("(type (arrow (u {level}) (arrow (u {level}) (u {level}))) (s {level}))");
        assert!(g.contains(&expected), "{g}");
        theory.check(&g, &p).unwrap();
    }
}

#[test]
fn a_fixed_level_beside_the_variable_still_generalizes() {
    // `nat` lives at level zero; max (s L) z (s L) holds for every L.
    let theory = format!("{THEORY}\n(ctor nat () T)\n(rule type.nat () (type nat z))");
    let goals = "(goal g (type (arrow (u z) nat) (s z)))";
    let proof = "
(step 0 type.u () (type (u z) (s z)))
(step 1 type.nat () (type nat z))
(step 2 max.sz () (max (s z) z (s z)))
(step 3 type.arrow (0 1 2) (type (arrow (u z) nat) (s z)))
(result g 3)
";
    let (goals_out, proof_out, rigid) = emit(&theory, goals, proof);
    assert!(rigid.is_empty(), "{rigid:?}");
    assert!(goals_out.contains("(type (arrow (u L) nat) (s L))"));
    check(&theory, &goals_out, proof_out.as_bytes()).unwrap();
}

#[test]
fn a_rule_that_pins_the_level_keeps_the_goal_ground() {
    let theory = THEORY.replace(
        "(rule type.u () (type (u ?l) (s ?l)))",
        "(rule type.u () (type (u z) (s z)))",
    );
    let (goals_out, proof_out, rigid) = emit(&theory, GOALS, PROOF);
    assert_eq!(rigid, ["arrow-of-universes"]);
    assert!(goals_out.contains("(type (arrow (u z) (arrow (u z) (u z))) (s z))"));
    check(&theory, &goals_out, proof_out.as_bytes()).unwrap();
}

#[test]
fn the_committed_schematic_example_and_its_agda_export_are_current() {
    let (goals, proof, _) = emit(THEORY, GOALS, PROOF);
    assert_eq!(goals, include_str!("../examples/levels.schematic.goals"));
    assert_eq!(proof, include_str!("../examples/levels.schematic.proof"));
    let mut out = Vec::new();
    export_agda(
        THEORY,
        &goals,
        proof.as_bytes(),
        "LevelsCertificate",
        &mut out,
    )
    .unwrap();
    let agda = String::from_utf8(out).unwrap();
    assert_eq!(agda, include_str!("../agda/LevelsCertificate.agda"));
}
