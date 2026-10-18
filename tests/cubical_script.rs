//! Cubical scripts: results are reported only from a kernel-checked oracle.
use horn::{cubical, oracle};

#[test]
fn transport_along_ua_of_not_evaluates_to_a_boolean() {
    let script = cubical::script::run(include_str!("../examples/cubical/script/bool.hcs")).unwrap();
    let shown: Vec<_> = script
        .evaluations
        .iter()
        .map(|e| format!("{} = {} : {}", e.name, e.value, e.ty))
        .collect();
    assert_eq!(shown, ["not-true = bfalse : bool", "along-ua = bfalse : bool"]);
    assert_eq!(script.certified.checked.goals, 6);
}

const NOT: &str = "
(def not (pi b bool bool) (lam b bool (bif c bool bfalse btrue b)))
(eval t (app not btrue))
(eval f (app not (app not btrue)))
(def not-not (pi b bool (path bool (app not (app not b)) b))
  (lam b bool (bif c (path bool (app not (app not c)) c) (plam i btrue) (plam i bfalse) b)))
(eval end (papp (app not-not bfalse) i1))
(check refl-true (plam i btrue) (path bool btrue btrue))
";

#[test]
fn evaluation_is_certified_and_reported() {
    let script = cubical::script::run(NOT).unwrap();
    let shown: Vec<_> = script
        .evaluations
        .iter()
        .map(|e| format!("{} = {} : {}", e.name, e.value, e.ty))
        .collect();
    assert_eq!(
        shown,
        ["t = bfalse : bool", "f = btrue : bool", "end = bfalse : bool"]
    );
    let c = &script.certified;
    assert_eq!(c.checked.goals, 6);
    oracle::check(&cubical::theory(), &c.goals, &c.oracle).unwrap();
    // The goal states the computed value; another value is rejected.
    let forged = c.goals.replace("(app (ann (lam (bif bool bfalse btrue (v z))) (pi bool bool)) btrue) bfalse bool)",
        "(app (ann (lam (bif bool bfalse btrue (v z))) (pi bool bool)) btrue) btrue bool)");
    assert_ne!(forged, c.goals);
    assert!(oracle::check(&cubical::theory(), &forged, &c.oracle).is_err());
}

#[test]
fn ill_typed_or_malformed_scripts_fail() {
    for bad in [
        // A boolean is not a function.
        "(def bad (pi b bool bool) (lam b bool (app btrue b)))",
        // The branches have the wrong motive.
        "(def bad (pi b bool (path bool b btrue)) (lam b bool (bif c (path bool c btrue) (plam i btrue) (plam i btrue) b)))",
        "(eval x (app missing btrue))",
        "(def not (pi b bool bool) (lam b bool b)) (def not (pi b bool bool) (lam b bool b))",
        "(def ua (u 0) bool)",
        "(eval x)",
    ] {
        assert!(cubical::script::run(bad).is_err(), "{bad}");
    }
}

#[test]
fn natural_number_programs_evaluate_and_induction_checks() {
    let script = cubical::script::run(include_str!("../examples/cubical/script/nat.hcs")).unwrap();
    let shown: Vec<_> = script
        .evaluations
        .iter()
        .map(|e| format!("{} = {} : {}", e.name, e.value, e.ty))
        .collect();
    assert_eq!(
        shown,
        [
            "two-plus-three = 5 : nat",
            "three-times-four = 12 : nat",
            "transport-nat = 6 : nat"
        ]
    );
    let add = "(def add (pi m nat (pi n nat nat))
        (lam m nat (lam n nat (natrec k nat m (lam k nat (lam r nat (suc r))) n))))";
    for bad in [
        // 0 + n is not suc n: the base case fails.
        "(def wrong (pi n nat (path nat (app add 0 n) (suc n)))
          (lam n nat (natrec k (path nat (app add 0 k) (suc k)) (plam i 1)
            (lam k nat (lam p (path nat (app add 0 k) (suc k)) (plam i (suc (papp p i))))) n)))",
        // A step that does not use the hypothesis cannot reach suc k.
        "(def wrong (pi n nat (path nat (app add 0 n) n))
          (lam n nat (natrec k (path nat (app add 0 k) k) (plam i 0)
            (lam k nat (lam p (path nat (app add 0 k) k) p)) n)))",
        // 2 + 2 is not 5.
        "(check wrong (plam i 5) (path nat (app add 2 2) 5))",
    ] {
        assert!(cubical::script::run(&format!("{add}\n{bad}")).is_err(), "{bad}");
    }
}

#[test]
fn a_function_transported_along_ua_computes() {
    let script =
        cubical::script::run(include_str!("../examples/cubical/script/function.hcs")).unwrap();
    let shown: Vec<_> = script
        .evaluations
        .iter()
        .map(|e| format!("{} = {} : {}", e.name, e.value, e.ty))
        .collect();
    // not conjugated by not is not again.
    assert_eq!(
        shown,
        ["moved-true = bfalse : bool", "moved-false = btrue : bool"]
    );
}

#[test]
fn declared_data_types_compute_and_move_along_ua() {
    let script = cubical::script::run(include_str!("../examples/cubical/script/data.hcs")).unwrap();
    let shown: Vec<_> = script
        .evaluations
        .iter()
        .map(|e| format!("{} = {} : {}", e.name, e.value, e.ty))
        .collect();
    assert_eq!(
        shown,
        [
            "after-red = green : color",
            "along-ua = green : color",
            "total = 6 : nat",
            "mirrored = (node leaf 2 (node leaf 1 leaf)) : tree"
        ]
    );
    // The generated rules travel with the certificate.
    let c = &script.certified;
    assert!(c.theory.contains("(rule req.comp-ty/color "));
    oracle::check(&c.theory, &c.goals, &c.oracle).unwrap();
    assert!(oracle::check(&cubical::theory(), &c.goals, &c.oracle).is_err());
}

#[test]
fn malformed_data_declarations_and_eliminations_fail() {
    let color = "(data color (red) (green))";
    for bad in [
        // Only discrete argument types are allowed.
        "(data box (mk (u 0)))",
        "(data box (mk later))",
        "(data box)",
        "(data two (a) (a))",
        "(data color (blue))",
        // Method count and method types are checked.
        "(def f (pi c color color) (lam c color (elim color k color (red) c)))",
        "(def f (pi c color nat) (lam c color (elim color k nat (red green) c)))",
        // A case analysis that does not prove its motive.
        "(def f (pi c color (path color c red))
           (lam c color (elim color k (path color k red) ((plam i red) (plam i red)) c)))",
        "(eval x (red green))",
    ] {
        assert!(cubical::script::run(&format!("{color}\n{bad}")).is_err(), "{bad}");
    }
}
