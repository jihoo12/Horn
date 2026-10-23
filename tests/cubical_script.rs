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
    assert_eq!(
        shown,
        ["not-true = bfalse : bool", "along-ua = bfalse : bool"]
    );
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
        [
            "t = bfalse : bool",
            "f = btrue : bool",
            "end = bfalse : bool"
        ]
    );
    let c = &script.certified;
    assert_eq!(c.checked.goals, 6);
    oracle::check(&c.theory, &c.goals, c.oracle.as_deref().unwrap()).unwrap();
    // The goal states the computed value; another value is rejected.
    let forged = c.goals.replace(
        "(app def/not btrue) bfalse bool)",
        "(app def/not btrue) btrue bool)",
    );
    assert_ne!(forged, c.goals);
    assert!(oracle::check(&c.theory, &forged, c.oracle.as_deref().unwrap()).is_err());
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
        assert!(
            cubical::script::run(&format!("{add}\n{bad}")).is_err(),
            "{bad}"
        );
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
    oracle::check(&c.theory, &c.goals, c.oracle.as_deref().unwrap()).unwrap();
    assert!(oracle::check(&cubical::theory(), &c.goals, c.oracle.as_deref().unwrap()).is_err());
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
        assert!(
            cubical::script::run(&format!("{color}\n{bad}")).is_err(),
            "{bad}"
        );
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
    assert!(
        script
            .certified
            .goals
            .contains("(goal swap-path (rhas z nil ft")
    );
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
        [
            "on-bool = btrue : bool",
            "on-types = bool : (u 0)",
            "twice-not = btrue : bool"
        ]
    );
    let names: Vec<_> = script.polymorphic.iter().map(|p| p.name.as_str()).collect();
    assert_eq!(
        names,
        ["id", "const", "twice", "ua-poly", "apply-id", "univalence"]
    );
    let theory = &script.certified.theory;
    for p in &script.polymorphic {
        // Every schematic certificate states its goal for the variable L.
        assert!(p.goals.starts_with("(var L N)"), "{}", p.name);
        assert!(p.goals.contains("(u L)"), "{}", p.name);
        horn::schematic::check(theory, &p.goals, p.proof.as_bytes()).unwrap();
    }
    // The univalence instance at L := 1 unfolds to a ground certificate that
    // the unchanged kernel accepts.
    let uv = script
        .polymorphic
        .iter()
        .find(|p| p.name == "univalence")
        .unwrap();
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
        .check(
            std::str::from_utf8(&goals).unwrap(),
            std::str::from_utf8(&proof).unwrap(),
        )
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
    assert!(
        c.rules_used.len() < declared.len() / 2,
        "{}",
        c.rules_used.len()
    );
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

#[test]
fn the_winding_number_of_loop_computes() {
    let script =
        cubical::script::run(include_str!("../examples/cubical/script/circle.hcs")).unwrap();
    let shown: Vec<_> = script
        .evaluations
        .iter()
        .map(|e| format!("{} = {} : {}", e.name, e.value, e.ty))
        .collect();
    assert_eq!(
        shown,
        [
            "loop-once = (pos 1) : int",
            "constant = (pos 0) : int",
            "loop-backwards = (negsuc 0) : int",
            "loop-twice = (pos 2) : int"
        ]
    );
    // The circle is not discrete: no rule reduces a composition in s1; it is
    // a formal point that only the recursor (req.s1rec-comp) takes apart.
    assert!(
        !script
            .certified
            .theory
            .contains("(req ?d ?g ?phi (comp s1 ")
    );
    assert!(
        script
            .certified
            .rules_used
            .iter()
            .any(|r| r == "req.s1rec-comp")
    );
}

/// The universe's line equivalence is generated text; regenerate the file
/// with `HORN_BLESS=1 cargo test canonical_map`.
#[test]
fn canonical_map_file_is_generated_and_typed_at_levels_0_1_2() {
    use cubical::engine::canonical_code_frontend::{definition, program};
    use cubical::engine::face_frontend::Face;
    use cubical::engine::restricted_frontend::RestrictedProducer;
    use cubical::engine::term::atom;
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/theories/cubical/canonical-map.horn"
    );
    let text = definition().unwrap();
    if std::env::var_os("HORN_BLESS").is_some() {
        std::fs::write(path, &text).unwrap();
    }
    assert_eq!(std::fs::read_to_string(path).unwrap(), text);
    let (certified, ()) = cubical::generate::certify(
        cubical::core_theory(),
        cubical::generate::Certificate::Direct,
        || {
            let mut p = RestrictedProducer::default();
            p.f.path.p.archive_judgments();
            p.reuse_restricted_typings();
            for l in 0..3 {
                let t = program(l)?;
                let (_, id) = p.infer(0, &atom("nil"), &Face::True, &t)?;
                p.f.path.p.result(&format!("canonical-map-{l}"), id);
            }
            Ok((p, (), String::new()))
        },
    )
    .unwrap();
    assert_eq!(certified.checked.goals, 3);
}

#[test]
fn declared_higher_inductive_types_compute() {
    let script = cubical::script::run(include_str!("../examples/cubical/script/hit.hcs")).unwrap();
    let shown: Vec<_> = script
        .evaluations
        .iter()
        .map(|e| format!("{} = {} : {}", e.name, e.value, e.ty))
        .collect();
    assert_eq!(
        shown,
        [
            "once = (pos 1) : int",
            "back = (negsuc 0) : int",
            "merid-true = (pos 1) : int",
            "merid-false = (pos 0) : int"
        ]
    );
    let used = &script.certified.rules_used;
    for rule in [
        "req.elim/circle.ctor/circle/lp",
        "req.ctor/susp/merid-1",
        "req.elim/susp.hcomp",
        "req.elim/trunc.ctor/trunc/squash",
        "req.ctor/trunc/squash-1",
        "req.ctor/glued/seg-0",
        "req.elim/glued.ctor/glued/seg",
    ] {
        assert!(used.iter().any(|r| r == rule), "{rule}");
    }
    // A higher inductive type is not discrete: no rule returns a base.
    assert!(
        !script
            .certified
            .theory
            .contains("(rule req.comp-ty/circle ")
    );
}

#[test]
fn parameterized_higher_inductive_types_transport_and_eliminate() {
    let script =
        cubical::script::run(include_str!("../examples/cubical/script/hit-params.hcs")).unwrap();
    let used = &script.certified.rules_used;
    for rule in [
        "req.comp-ty/susp.ctor/susp/merid",
        "req.comp-ty/ptrunc.ctor/ptrunc/squash",
        "req.elim/ptrunc.hcomp",
        "req.elim/ptrunc.ctor/ptrunc/squash",
        "req.ctor/ptrunc/squash-0",
    ] {
        assert!(used.iter().any(|r| r == rule), "{rule}");
    }
}

/// A constructor whose fields leave a parameter open has no single type, so
/// checking it at one does not make that type its inferred one.
#[test]
fn constructors_with_open_parameters_keep_every_type() {
    let source = "(data (box A) (z) (s (box A)))
      (data (susp A) (north) (south) (merid A (path north south)))
      (def f (pi x (box nat) (box bool))
        (lam x (box nat) (elim box (nat) k (box bool) ((s z) (lam y (box nat) (lam h (box bool) (s h)))) x)))
      (equal e (app f (s z)) (s (s z)) (box bool))
      (equal m (elim susp (nat) k (susp bool) (north south (lam a nat (plam i (merid btrue i)))) (merid 3 i0))
        north (susp bool))";
    cubical::script::run(source).unwrap();
    // A parameter field whose own type is open does not fix the parameter.
    let nested = "(data (box A) (z)) (data (wrap A) (w A))
      (check c (w z) (wrap (box nat)))
      (eval e (w z))";
    assert!(cubical::script::run(nested).is_err());
}

/// The eliminator on a transport along a varying family reduces the
/// transport constructorwise; only a homogeneous composition is formal.
#[test]
fn eliminating_a_transport_in_a_parameterized_higher_type_reduces_it() {
    let source = "(data (susp A) (north) (south) (merid A (path north south)))
      (def P (path (u 0) nat nat) (plam i nat))
      (equal r (elim susp (nat) k bool (btrue btrue (lam a nat (plam i btrue)))
          (transport j (susp (papp P j)) north))
        btrue bool)";
    cubical::script::run(source).unwrap();
}

#[test]
fn path_constructors_are_restricted_to_point_endpoints() {
    for bad in [
        "(data (t A) (a A) (p (x A) (path (a x) a)))",
        "(data (t A) (a A) (p (x A) (path (a btrue) (a x))))",
        "(data t (a) (p (path a q)))",
        "(data t (a) (p (path a a)) (q (path p a)))",
        // An endpoint field must have the type of its position.
        "(data t (a nat) (p (n nat) (path n (a 0))))",
        "(data t (a nat) (b bool) (p (n bool) (path (a n) (b n))))",
        "(data t (a nat) (p (x t) (path (a x) x)))",
        "(data t (a) (p (x t) (x t) (path x x)))",
    ] {
        assert!(cubical::script::run(bad).is_err(), "{bad}");
    }
}

/// A composition binder may shadow an outer dimension: the branch faces and
/// a homogeneous type are written outside its scope.
#[test]
fn composition_binders_do_not_capture_outer_faces_or_types() {
    for source in [
        "(check shadow-face (plam i (hcomp i nat (((= i 0) zero)) zero)) (path nat zero zero))",
        "(check shadow-family
           (lam P (path (u 0) nat nat) (plam i (lam x (papp P i) (hcomp i (papp P i) () x))))
           (pi P (path (u 0) nat nat)
             (path i (pi x (papp P i) (papp P i)) (lam x nat x) (lam x nat x))))",
    ] {
        let script = cubical::script::run(source).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(script.certified.checked.goals, 1);
    }
}

const ADD: &str = "(def add (pi m nat (pi n nat nat))
  (lam m nat (lam n nat (natrec k nat m (lam k nat (lam r nat (suc r))) n))))";

#[test]
fn holes_show_every_goal_by_name_with_path_boundaries() {
    let source = format!(
        "{ADD}
(def zero-add (pi n nat (path nat (app add 0 n) n))
  (lam n nat
    (natrec k (path nat (app add 0 k) k)
      (plam i ?)
      (lam k nat (lam p (path nat (app add 0 k) k) (? step)))
      n)))"
    );
    let Err(err) = cubical::script::run(&source) else {
        panic!("a form with holes must not be certified");
    };
    let expected = "def zero-add: 2 goals to fill

?1
  n : nat
  i : I
  ⊢ nat
  where i = 0 must give (app add 0 0)
        i = 1 must give 0

?step
  n : nat
  k : nat
  p : (path nat (app add 0 k) k)
  ⊢ (path nat (app add 0 (suc k)) (suc k))";
    assert_eq!(err, expected);
    // Filling both holes gives a checked proof.
    let filled = source
        .replace("(plam i ?)", "(plam i 0)")
        .replace("(? step)", "(plam i (suc (papp p i)))");
    cubical::script::run(&filled).unwrap();
}

#[test]
fn holes_report_faces_shadowing_and_unknown_types() {
    let side = cubical::script::run(
        "(def compose (pi p (path s1 base base) (pi q (path s1 base base) (path s1 base base)))
  (lam p (path s1 base base) (lam q (path s1 base base)
    (plam i (hcomp j s1 (((= i 0) base) ((= i 1) (? side))) (papp p i))))))",
    )
    .err()
    .unwrap();
    assert!(
        side.contains("  i j : I\n  under (= i 1)\n  ⊢ s1"),
        "{side}"
    );
    let shadow =
        cubical::script::run("(def shadow (pi x nat (pi x nat nat)) (lam x nat (lam x nat ?)))")
            .err()
            .unwrap();
    assert!(
        shadow.ends_with("  x✝ : nat\n  x : nat\n  ⊢ nat"),
        "{shadow}"
    );
    let head = cubical::script::run("(eval three (app ? 1 2))")
        .err()
        .unwrap();
    assert!(head.contains("its type is not known here"), "{head}");
}

#[test]
fn holes_in_equalities_types_and_unreached_positions_are_all_reported() {
    let equal = cubical::script::run("(equal e ? ? nat)").err().unwrap();
    assert_eq!(
        equal,
        "equal e: 2 goals to fill\n\n?1\n  ⊢ nat\n\n?2\n  ⊢ nat\n\nand these must hold:\n  ?1 = ?2 : nat"
    );
    let app = cubical::script::run("(eval x (app ? ?))").err().unwrap();
    assert!(app.starts_with("eval x: 2 goals to fill"), "{app}");
    assert!(app.contains("?2\n  (not reached by the checker"), "{app}");
    // Holes inside a goal print as written, not as internal numbers.
    let path = cubical::script::run("(def x (path ? ? ?) (plam i ?))")
        .err()
        .unwrap();
    assert!(
        path.ends_with(
            "?4\n  i : I\n  ⊢ ?1\n  where i = 0 must give ?2\n        i = 1 must give ?3"
        ),
        "{path}"
    );
    // A shadowed dimension is marked like a shadowed variable.
    let dims = cubical::script::run(
        "(def shade (path (path nat 0 0) (plam i 0) (plam i 0)) (plam i (plam i ?)))",
    )
    .err()
    .unwrap();
    assert!(dims.contains("\n  i✝ i : I\n"), "{dims}");
}

#[test]
fn holes_are_numbered_in_source_order_and_never_certified() {
    // A hole in a lambda's domain, which the elaborator does not use, still
    // keeps the form from being certified.
    let domain = cubical::script::run("(check x (lam n ? n) (pi n nat nat))")
        .err()
        .unwrap();
    assert!(
        domain.contains("?1\n  (in a position that is not checked"),
        "{domain}"
    );
    // `check` elaborates the type first; numbers follow the source.
    let both = cubical::script::run("(check both ? ?)").err().unwrap();
    assert!(
        both.starts_with("check both: 2 goals to fill\n\n?1\n  ⊢ ?2"),
        "{both}"
    );
    // A def-poly elaborates its source twice; its hole is one goal.
    let poly = cubical::script::run("(def-poly id (L) (pi A (u L) (pi x A A)) (? todo))")
        .err()
        .unwrap();
    assert!(
        poly.starts_with("def-poly id: 1 goal to fill\n\n?todo\n"),
        "{poly}"
    );
    // A hole under an annotation still owes the path's ends.
    let ann = cubical::script::run("(def x (path nat 0 0) (plam i (ann ? nat)))")
        .err()
        .unwrap();
    assert!(
        ann.ends_with("where i = 0 must give 0\n        i = 1 must give 0"),
        "{ann}"
    );
}

#[test]
fn def_poly_goals_show_the_level_variable_and_annotations_are_respected() {
    let level = cubical::script::run("(def-poly x (L) (u L) ?)")
        .err()
        .unwrap();
    assert_eq!(level, "def-poly x: 1 goal to fill\n\n?1\n  ⊢ (u L)");
    let body = cubical::script::run(
        "(def-poly id (L) (pi A (u L) (pi x A A)) (lam A (u L) (lam x A (? body))))",
    )
    .err()
    .unwrap();
    assert!(
        body.ends_with("?body\n  A : (u L)\n  x : A\n  ⊢ A"),
        "{body}"
    );
    // An annotation other than the path's family is the hole's type, and
    // the hole is not given the path's ends.
    let other = cubical::script::run("(def x (path nat 0 0) (plam i (ann ? bool)))")
        .err()
        .unwrap();
    assert!(other.ends_with("i : I\n  ⊢ bool"), "{other}");
}

#[test]
fn goals_keep_equations_and_say_when_their_type_is_not_a_type() {
    let value = cubical::script::run("(def x btrue ?)").err().unwrap();
    assert!(
        value.ends_with("⊢ btrue  (not a type, so nothing can fill this)"),
        "{value}"
    );
    for bad in [
        "(def x (path btrue btrue btrue) (plam i ?))",
        "(def x (path nat btrue btrue) (plam i ?))",
    ] {
        let path = cubical::script::run(bad).err().unwrap();
        assert!(
            path.contains("(but the path type it is in is not a type"),
            "{path}"
        );
    }
    let equation = cubical::script::run("(equal e ? 0 nat)").err().unwrap();
    assert_eq!(
        equation,
        "equal e: 1 goal to fill\n\n?1\n  ⊢ nat\n\nand these must hold:\n  ?1 = 0 : nat"
    );
}

#[test]
fn equations_outside_a_path_and_holes_in_declarations_read_well() {
    let ends =
        cubical::script::run("(def f (pi n nat (path nat n n)) (lam n nat (plam i (suc ?))))")
            .err()
            .unwrap();
    assert!(ends.contains("(suc ?1) = n : nat"), "{ends}");
    // Equations name their variables after the holes they contain.
    let two = cubical::script::run(
        "(def f (sigma p (pi a nat (path nat a a)) (pi b nat (path nat b b)))
           (pair (lam a nat (plam i (suc ?))) (lam b nat (plam j (suc ?)))))",
    )
    .err()
    .unwrap();
    assert!(two.contains("(suc ?1) = a : nat"), "{two}");
    assert!(two.contains("(suc ?2) = b : nat"), "{two}");
    let field = cubical::script::run("(data t (a ?))").err().unwrap();
    assert!(
        field.contains("?1\n  (in a position that is not checked"),
        "{field}"
    );
    let data = cubical::script::run("(data t (a nat) (p (path (a ?) (a 0))))")
        .err()
        .unwrap();
    assert!(
        data.ends_with(
            "(in a position that is not checked (a lambda's domain, a data declaration); write it out)"
        ),
        "{data}"
    );
}

#[test]
fn wrong_proofs_say_what_is_wrong_by_name() {
    // A missing `suc` in the induction step: the path starts in the wrong place.
    let step = cubical::script::run(&format!(
        "{ADD}
(def zero-add (pi n nat (path nat (app add 0 n) n))
  (lam n nat
    (natrec k (path nat (app add 0 k) k)
      (plam i 0)
      (lam k nat (lam p (path nat (app add 0 k) k) (plam i (papp p i))))
      n)))"
    ))
    .err()
    .unwrap();
    assert!(
        step.starts_with("def zero-add: the path does not end where it must, at i = 0"),
        "{step}"
    );
    assert!(
        step.contains("\n  p : (path nat (app add 0 k) k)\n"),
        "{step}"
    );
    assert!(
        step.contains("\n  it is (papp p 0), which computes to "),
        "{step}"
    );
    assert!(
        step.contains("\n  but must be (app add 0 (suc k)), which computes to (suc "),
        "{step}"
    );
    let ty = cubical::script::run(&format!(
        "{ADD}\n(def bad (pi n nat bool) (lam n nat (app add n 1)))"
    ))
    .err()
    .unwrap();
    assert_eq!(
        ty,
        "def bad: a term does not have the type it must

  n : nat

  the term (app add n 1)
  has type nat
  but must have bool"
    );
    let former = cubical::script::run("(def notfun nat (lam x nat x))")
        .err()
        .unwrap();
    assert!(
        former.starts_with("def notfun: a function (lam) cannot have this type"),
        "{former}"
    );
}

#[test]
fn implicit_arguments_are_inferred_from_explicit_ones() {
    cubical::script::run(include_str!("../examples/cubical/script/implicit.hcs")).unwrap();
    let sym = "(def sym (pi {A} (u 0) (pi {x} A (pi {y} A (pi p (path A x y) (path A y x)))))
      (lam p (path A x y) (plam i (papp p (neg i)))))";
    for (bad, says) in [
        // A bare reference leaves them open.
        ("(check a sym (path nat 0 0))", "implicit arguments"),
        // An unannotated lambda has no type to read them from.
        (
            "(check b (app sym (lam x nat x)) (path nat 0 0))",
            "cannot infer",
        ),
        // Only a def's type starts with implicit binders.
        ("(check c (pi {A} (u 0) A) (u 1))", "implicit binder"),
        // A wrong guess is still checked.
        ("(check d (app sym (plam i 1)) (path nat 0 0))", "must have"),
        // A family that uses the path's own dimension is no solution.
        (
            "(def P (path (u 0) nat nat) (plam i nat))
             (check e (app sym (ann (plam i 0) (path i (papp P i) 0 0))) (path nat 0 0))",
            "cannot infer",
        ),
    ] {
        let err = cubical::script::run(&format!("{sym}\n{bad}"))
            .err()
            .unwrap();
        assert!(err.contains(says), "{bad}: {err}");
    }
    // A solution under the domain's path binder may use an outer dimension,
    // which moves out with it.
    let outer = "(def P (path (u 0) nat nat) (plam i nat))
      (check outer (plam r (app sym (ann (plam i 0) (path (papp P r) 0 0))))
        (path i (path (papp P i) 0 0) (plam i 0) (plam i 0)))";
    cubical::script::run(&format!("{sym}\n{outer}")).unwrap();
}

/// Eta, congruence and beta at types that only compute to a former: a
/// definition applied to arguments, as morphism types of a category are.
#[test]
fn types_that_compute_to_a_former_support_eta_and_beta() {
    let defs = "(def H (pi x (u 0) (pi y (u 0) (u 0))) (lam x (u 0) (lam y (u 0) (pi z x y))))
      (def I (pi x (u 0) (app H x x)) (lam A (u 0) (lam a A a)))";
    for goal in [
        // Eta at (app H A A), a redex for a pi.
        "(check eta (lam A (u 0) (lam f (app H A A) (plam i f)))
           (pi A (u 0) (pi f (app H A A) (path (app H A A) (lam x A (app f x)) f))))",
        // Beta through I's annotation, which computes to a pi, inside a
        // lambda compared at (app H A B).
        "(check beta (lam A (u 0) (lam B (u 0) (lam f (app H A B) (plam i f))))
           (pi A (u 0) (pi B (u 0) (pi f (app H A B)
             (path (app H A B) (lam x A (app f (app I A x))) f)))))",
    ] {
        cubical::script::run(&format!("{defs}\n{goal}")).unwrap();
    }
}

/// A category as a nested Sigma: the category of types satisfies its laws,
/// and the opposite of any category is one. A component substituted into a
/// later component's type under binders recovers the type it was checked at.
#[test]
fn categories_and_their_opposites_check() {
    cubical::script::run(include_str!("../examples/cubical/script/category.hcs")).unwrap();
}

/// A definition is a constant whose typing and unfolding rules both need
/// the definition's own closed typing: a definitional extension. Later forms
/// mention it by its constant, not a copy of its body.
#[test]
fn definitions_are_constants_with_premised_rules() {
    let script = cubical::script::run(
        "(def two nat 2)
         (def double (pi n nat nat) (lam n nat (natrec k nat 0 (lam k nat (lam r nat (suc (suc r)))) n)))
         (eval four (app double two))",
    )
    .unwrap();
    assert_eq!(script.evaluations[0].value, "4");
    let theory = &script.certified.theory;
    let body = "(rhas z nil ft (suc (suc zero)) nat)";
    for rule in [
        format!("(rule rhas.def/two ((rctx ?d ?g ?phi) {body}) (rhas ?d ?g ?phi def/two nat))"),
        format!(
            "(rule req.delta.def/two ((rctx ?d ?g ?phi) {body}) (req ?d ?g ?phi def/two (suc (suc zero)) nat))"
        ),
    ] {
        assert!(theory.contains(&rule), "{rule}");
    }
    assert!(script.certified.goals.contains("(app def/double def/two)"));
    let used = &script.certified.rules_used;
    assert!(used.iter().any(|r| r == "req.delta.def/double"));
}

/// An equation is derived in the shortest context its terms live in and
/// lifted by req.shift, rather than derived again under each binder: here
/// the codomains of two pi types are compared under a binder they ignore.
#[test]
fn equations_are_derived_once_and_lifted_under_binders() {
    let script = cubical::script::run(
        "(def idn (pi n nat nat) (lam n nat n))
         (check deep (lam a nat (lam f (pi n nat (path nat (app idn a) a)) f))
           (pi a nat (pi f (pi n nat (path nat (app idn a) a)) (pi n nat (path nat a a)))))",
    )
    .unwrap();
    assert!(script.certified.rules_used.iter().any(|r| r == "req.shift"));
}
