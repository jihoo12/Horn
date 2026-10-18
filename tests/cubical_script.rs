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
    oracle::check(&c.theory, &c.goals, &c.oracle).unwrap();
    // The goal states the computed value; another value is rejected.
    let forged = c.goals.replace("(app (ann (lam (bif bool bfalse btrue (v z))) (pi bool bool)) btrue) bfalse bool)",
        "(app (ann (lam (bif bool bfalse btrue (v z))) (pi bool bool)) btrue) btrue bool)");
    assert_ne!(forged, c.goals);
    assert!(oracle::check(&c.theory, &forged, &c.oracle).is_err());
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

#[test]
fn parameterized_lists_compute_and_move_along_ua() {
    let script = cubical::script::run(include_str!("../examples/cubical/script/list.hcs")).unwrap();
    let shown: Vec<_> = script
        .evaluations
        .iter()
        .map(|e| format!("{} = {} : {}", e.name, e.value, e.ty))
        .collect();
    assert_eq!(
        shown,
        [
            "len = 2 : nat",
            "mapped = (cons bfalse (cons btrue nil)) : (list bool)",
            "moved = (cons bfalse (cons bfalse nil)) : (list bool)"
        ]
    );
    let theory = &script.certified.theory;
    // Transport rules only: no rule returns the base of a composition in a
    // parameterized type.
    assert!(theory.contains("(rule req.comp-ty/list.ctor/list/cons "));
    assert!(!theory.contains("(rule req.comp-ty/list ("));
}

#[test]
fn malformed_parameterized_declarations_fail() {
    for bad in [
        // Non-uniform recursion and unknown parameters.
        "(data (list A) (nil) (cons A (list bool)))",
        "(data (list A) (nil) (cons B (list A)))",
        "(data (pair A A) (mk A A))",
        // A bare nil has no type to read its parameter from.
        "(data (list A) (nil) (cons A (list A))) (eval x nil)",
        "(data (list A) (nil) (cons A (list A))) (check x (nil bool) (list bool))",
        // Fields must agree with the expected parameter.
        "(data (list A) (nil) (cons A (list A))) (check x (cons zero nil) (list bool))",
        "(data (list A) (nil) (cons A (list A))) (check x (cons btrue (cons zero nil)) (list bool))",
    ] {
        assert!(cubical::script::run(bad).is_err(), "{bad}");
    }
}

#[test]
fn univalence_one_universe_up_computes_on_data_results() {
    let script =
        cubical::script::run(include_str!("../examples/cubical/script/levels.hcs")).unwrap();
    let shown: Vec<_> = script
        .evaluations
        .iter()
        .map(|e| format!("{} = {} : {}", e.name, e.value, e.ty))
        .collect();
    assert_eq!(shown, ["applied = btrue : bool"]);
    assert!(script.certified.goals.contains("(goal swap-path (rhas z nil ft"));
}

#[test]
fn level_polymorphic_definitions_hold_at_every_level() {
    let script = cubical::script::run(include_str!("../examples/cubical/script/poly.hcs")).unwrap();
    let shown: Vec<_> = script
        .evaluations
        .iter()
        .map(|e| format!("{} = {} : {}", e.name, e.value, e.ty))
        .collect();
    assert_eq!(
        shown,
        ["on-bool = btrue : bool", "on-types = bool : (u 0)", "twice-not = btrue : bool"]
    );
    let names: Vec<_> = script.polymorphic.iter().map(|p| p.name.as_str()).collect();
    assert_eq!(names, ["id", "const", "twice", "ua-poly", "apply-id", "univalence"]);
    let theory = &script.certified.theory;
    for p in &script.polymorphic {
        // Every schematic certificate states its goal for the variable L.
        assert!(p.goals.starts_with("(var L N)"), "{}", p.name);
        assert!(p.goals.contains("(u L)"), "{}", p.name);
        horn::schematic::check(theory, &p.goals, p.proof.as_bytes()).unwrap();
    }
    // The univalence instance at L := 1 unfolds to a ground certificate that
    // the unchanged kernel accepts.
    let uv = script.polymorphic.iter().find(|p| p.name == "univalence").unwrap();
    let (mut goals, mut proof) = (Vec::new(), Vec::new());
    horn::schematic::instantiate(
        theory,
        &uv.goals,
        uv.proof.as_bytes(),
        &[("L".into(), "(s z)".into())],
        &mut goals,
        &mut proof,
    )
    .unwrap();
    let report = horn::kernel::Theory::parse(theory)
        .unwrap()
        .check(std::str::from_utf8(&goals).unwrap(), std::str::from_utf8(&proof).unwrap())
        .unwrap();
    assert_eq!(report.goals, 1);
}

#[test]
fn definitions_that_pin_their_level_are_not_polymorphic() {
    for bad in [
        // bool lives in U0 only.
        "(def-poly bad (L) (u L) bool)",
        "(def-poly bad (L) (pi A (u L) (u L)) (lam A (u L) nat))",
        // One level parameter.
        "(def-poly bad (L M) (u L) bool)",
        "(eval x (at missing 0))",
    ] {
        assert!(cubical::script::run(bad).is_err(), "{bad}");
    }
}

#[test]
fn a_result_reports_the_rules_it_relies_on() {
    let script = cubical::script::run(include_str!("../examples/cubical/script/nat.hcs")).unwrap();
    let c = &script.certified;
    let declared: std::collections::HashSet<String> = horn::sexp::parse(&c.theory)
        .unwrap()
        .iter()
        .filter_map(|f| {
            let xs = f.list().ok()?;
            (xs.first()?.atom().ok()? == "rule").then(|| xs[1].atom().unwrap().to_owned())
        })
        .collect();
    assert!(c.rules_used.iter().all(|r| declared.contains(r)));
    // Natural-number programs need none of the Glue rules.
    assert!(c.rules_used.iter().any(|r| r == "req.natrec-suc"));
    assert!(!c.rules_used.iter().any(|r| r.contains("glue")));
    assert!(c.rules_used.len() < declared.len() / 2, "{}", c.rules_used.len());
}

#[test]
fn addition_transported_to_binary_numbers_computes() {
    let script =
        cubical::script::run(include_str!("../examples/cubical/script/binary.hcs")).unwrap();
    let shown: Vec<_> = script
        .evaluations
        .iter()
        .map(|e| format!("{} = {} : {}", e.name, e.value, e.ty))
        .collect();
    // 5 = 2*2 + 1 and 2 = 2*0 + 2 in bijective base 2.
    assert_eq!(
        shown,
        [
            "three = 3 : nat",
            "five = (b1 (b2 bz)) : bin",
            "three-plus-two = (b1 (b2 bz)) : bin"
        ]
    );
}
