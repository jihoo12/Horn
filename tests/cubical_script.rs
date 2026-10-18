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
