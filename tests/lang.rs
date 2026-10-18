//! The surface language: elaboration, evaluation, proof search, and the
//! certificate it produces.
use horn::{lang, schematic};

const NAT: &str = include_str!("../examples/lang/nat.hn");
const LE: &str = include_str!("../examples/lang/le.hn");

#[test]
fn the_example_evaluates_and_proves() {
    let r = lang::run(NAT).unwrap();
    let report = r.report.join("\n");
    for line in [
        "add 2 3  ⟹  5",
        "double 4  ⟹  8",
        "add 3 2 = 5  with ?x = 3",
        "le 2 4  ✓",
        "theorem add_zero : add n 0 = n  ✓ (by induction n)",
        "theorem le_refl : le n n  ✓ (by induction n)",
        "theorem lt_succ : lt n (succ n)  ✓ (by auto)",
    ] {
        assert!(report.contains(line), "missing {line:?} in\n{report}");
    }
    assert_eq!(r.checked.goals, 10);
    // The certificate stands on its own.
    schematic::check(&r.theory, &r.goals, r.proof.as_bytes()).unwrap();
}

#[test]
fn the_committed_agda_export_is_current() {
    let r = lang::run(NAT).unwrap();
    let mut out = Vec::new();
    schematic::export_agda(&r.theory, &r.goals, r.proof.as_bytes(), "NatLang", &mut out).unwrap();
    assert_eq!(
        String::from_utf8(out).unwrap(),
        include_str!("../agda/NatLang.agda")
    );
}

fn fails(src: &str, reason: &str) {
    match lang::run(src) {
        Ok(_) => panic!("accepted, expected: {reason}"),
        Err(e) => assert!(e.contains(reason), "failed for another reason: {e}"),
    }
}

const BASE: &str = "
sort Nat
ctor zero : Nat
ctor succ : Nat → Nat
pred le : Nat → Nat → Prop
rule le.zero : le zero n
rule le.succ : le m n → le (succ m) (succ n)
def add : Nat → Nat → Nat
| zero,   n => n
| succ m, n => succ (add m n)
";

#[test]
fn false_statements_are_not_proved() {
    fails(
        &format!("{BASE}theorem bad (n : Nat) : le (succ n) n"),
        "could not prove bad",
    );
    fails(&format!("{BASE}#check le 3 1"), "no derivation found");
}

#[test]
fn mistakes_are_reported() {
    fails(&format!("{BASE}#check lt 1 2"), "unknown");
    fails(
        &format!("{BASE}#check le (add 1 1) 2"),
        "is called inside a term",
    );
    fails(&format!("{BASE}theorem t : le n n"), "is not bound");
    fails("sort Nat\nsort Nat", "already declared");
}

#[test]
fn declarations_alone_and_unconstrained_rule_variables_are_fine() {
    lang::run(&format!("{BASE}pred p : Prop\nrule odd : p")).unwrap();
    let ok = format!("{BASE}pred p : Nat → Prop\nrule all : p n\n#check p 2");
    lang::run(&ok).unwrap();
}

#[test]
fn implications_are_proved_by_induction_and_inversion() {
    let r = lang::run(LE).unwrap();
    let report = r.report.join("\n");
    for line in [
        "theorem le_pred : le (succ m) (succ n) → le m n  ✓ (by auto)",
        "theorem not_succ_le_zero : le (succ n) 0 → le 1 0  ✓ (by auto)",
        "theorem le_trans : le a b → le b c → le a c  ✓ (by induction a)",
        "theorem add_succ : add m n = r1 → add m (succ n) = succ r1  ✓ (by induction m)",
        "theorem le_add : add m n = r1 → le n r1  ✓ (by induction m)",
    ] {
        assert!(report.contains(line), "missing {line:?} in\n{report}");
    }
    assert_eq!(r.checked.goals, 7);
    assert!(r.checked.inversions > 0);
    assert!(r.goals.contains("(goal le_trans ((le le_trans.a le_trans.b) (le le_trans.b le_trans.c)) (le le_trans.a le_trans.c))"));
    schematic::check(&r.theory, &r.goals, r.proof.as_bytes()).unwrap();
}

#[test]
fn false_implications_are_not_proved() {
    fails(
        &format!("{BASE}theorem bad (a b : Nat) : le a b → le b a"),
        "could not prove bad",
    );
    fails(
        &format!("{BASE}theorem bad (n : Nat) : le n zero → le (succ zero) n"),
        "could not prove bad",
    );
}

#[test]
fn an_implication_is_used_as_a_lemma() {
    let src = format!(
        "{BASE}theorem le_pred (m n : Nat) : le (succ m) (succ n) → le m n\n\
         theorem le_pred2 (m n : Nat) : le (succ (succ m)) (succ (succ n)) → le m n := by auto"
    );
    let r = lang::run(&src).unwrap();
    assert!(r.proof.contains("(apply "), "{}", r.proof);
}
