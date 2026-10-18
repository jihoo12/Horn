use horn::{
    cubical::{
        ast::Face,
        producer::{self, Judgment, Profile, Request},
        source,
    },
    kernel::Theory,
};

fn evaluate(f: &Face, assignment: &[u8; 2]) -> bool {
    match f {
        Face::False => false,
        Face::True => true,
        Face::End(n, one) => assignment[*n] == if *one { 2 } else { 1 },
        Face::And(a, b) => evaluate(a, assignment) && evaluate(b, assignment),
        Face::Or(a, b) => evaluate(a, assignment) || evaluate(b, assignment),
    }
}

fn implication(a: &Face, b: &Face) -> bool {
    // 0 denotes an unspecified/generic dimension; endpoint cases alone would
    // incorrectly validate (i=0) ∨ (i=1) = true.
    (0..3).all(|i| (0..3).all(|j| !evaluate(a, &[i, j]) || evaluate(b, &[i, j])))
}

#[test]
fn emitted_face_derivations_agree_with_independent_partial_assignments() {
    let mut pool = vec![
        Face::False,
        Face::True,
        Face::End(0, false),
        Face::End(0, true),
        Face::End(1, false),
        Face::End(1, true),
    ];
    let mut state = 42u64;
    let mut next = |n: usize| {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        (state >> 32) as usize % n
    };
    for _ in 0..24 {
        let a = Box::new(pool[next(pool.len())].clone());
        let b = Box::new(pool[next(pool.len())].clone());
        pool.push(if next(2) == 0 {
            Face::And(a, b)
        } else {
            Face::Or(a, b)
        });
    }
    for _ in 0..160 {
        let a = pool[next(pool.len())].clone();
        let b = pool[next(pool.len())].clone();
        let expected = implication(&a, &b);
        let request = Request {
            name: "test".into(),
            dimensions: 2,
            context: vec![],
            judgment: Judgment::Entails {
                premise: a.clone(),
                conclusion: b.clone(),
            },
        };
        let result = producer::produce(&[request]);
        assert_eq!(result.is_ok(), expected, "{} -> {}", a.quote(), b.quote());
        if let Ok(out) = result {
            assert_eq!(out.profile, Profile::Faces);
            Theory::parse(&out.theory)
                .unwrap()
                .check(&out.goals, &out.proof)
                .unwrap();
        }
    }
}

#[test]
fn endpoint_and_compound_interval_faces_have_checked_local_equalities() {
    let out = source::run(include_str!("../examples/cubical/source/faces.hcu")).unwrap();
    assert_eq!(out.checked.goals, 9);
    assert_eq!(out.profile, Profile::Faces);
    assert!(out.proof.contains("cover.or-left"));
    assert!(out.proof.contains("boundary.meet"));
    assert!(out.proof.contains("local.meet"));
    Theory::parse(&out.theory)
        .unwrap()
        .check(&out.goals, &out.proof)
        .unwrap();
    let forged = out.proof.replace("entails.checked", "invented.entails");
    assert!(
        Theory::parse(&out.theory)
            .unwrap()
            .check(&out.goals, &forged)
            .is_err()
    );
}

#[test]
fn faces_do_not_admit_boolean_excluded_middle_or_scope_leaks() {
    for src in [
        "(entails excluded-middle (scope (i) ()) ft (for (at0 i) (at1 i)))",
        "(entails false-implication (scope (i) ()) (at0 i) (at1 i))",
        "(entails free-dimension ff (at0 0))",
        "(local wrong (scope (i) ()) ft i i0)",
        "(local wrong-endpoint (scope (i) ()) (at0 i) i i1)",
        "(local free ff (dim 0) i0)",
        "(entails ordinary-is-not-dimension (scope () ((i nat))) ft (at0 i))",
    ] {
        let err = source::run(src)
            .err()
            .unwrap_or_else(|| panic!("accepted {src}"));
        assert!(!err.contains("generated certificate rejected"), "{err}");
    }
}
