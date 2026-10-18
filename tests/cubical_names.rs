use horn::cubical::{producer, source};
use horn::kernel::Theory;

fn same(named: &str, core: &str) {
    let named = source::run(named).unwrap();
    let core = source::run(core).unwrap();
    assert_eq!(named.goals, core.goals);
    assert_eq!(named.proof, core.proof);
    Theory::parse(producer::THEORY)
        .unwrap()
        .check(&named.goals, &named.proof)
        .unwrap();
}

#[test]
fn named_dependent_functions_have_the_exact_explicit_core_evidence() {
    same(
        "(check id (lam A (u 0) (lam x A x)) (pi A (u 0) (pi x A A)))",
        "(check id (lam (u 0) (lam (v 0) (v 0))) (pi (u 0) (pi (v 0) (v 1))))",
    );
    same(
        "(check shadow (lam x nat (lam x nat x)) (pi x nat (pi y nat nat)))",
        "(check shadow (lam nat (lam nat (v 0))) (pi nat (pi nat nat)))",
    );
    same(
        "(check mixed (lam x nat (lam nat x)) (pi nat (pi nat nat)))",
        "(check mixed (lam nat (lam nat (v 1))) (pi nat (pi nat nat)))",
    );
}

#[test]
fn named_dimensions_survive_ordinary_and_anonymous_dimension_binders() {
    same(
        "(check p (scope (i) ((p (path nat zero zero)))) (plam nat (papp p i)) (path nat (papp p i) (papp p i)))",
        "(check p (scope 1 ((path nat zero zero))) (plam nat (papp (v 0) (dim 1))) (path nat (papp (v 0) (dim 0)) (papp (v 0) (dim 0))))",
    );
    same(
        "(check p (scope (i) ((p (path nat zero zero)))) (lam x nat (papp p i)) (pi nat nat))",
        "(check p (scope 1 ((path nat zero zero))) (lam nat (papp (v 1) (dim 0))) (pi nat nat))",
    );
    same(
        "(check separate (lam x nat (plam x nat x)) (pi nat (path nat (v 0) (v 0))))",
        "(check separate (lam nat (plam nat (v 0))) (pi nat (path nat (v 0) (v 0))))",
    );
    same(
        "(check shadow (scope (i) ((p (path nat zero zero)))) (plam i nat (papp p i)) (path nat (papp p i0) (papp p i1)))",
        "(check shadow (scope 1 ((path nat zero zero))) (plam nat (papp (v 0) (dim 0))) (path nat (papp (v 0) i0) (papp (v 0) i1)))",
    );
}

#[test]
fn named_contexts_resolve_dependencies_at_binding_sites() {
    same(
        "(check x (scope () ((A (u 0)) (x A))) x A)",
        "(check x (scope 0 ((u 0) (v 0))) (v 0) (v 1))",
    );
    let out = source::run(include_str!("../examples/cubical/source/named.hcu")).unwrap();
    assert_eq!(out.checked.goals, 6);
}

#[test]
fn names_cannot_escape_binders_or_cross_namespaces() {
    for source in [
        "(check bad (lam x x x) nat)",
        "(check first (lam x nat x) (pi nat nat)) (check second x nat)",
        "(check bad (scope () ((x A) (A (u 0)))) x nat)",
        "(check bad (scope () ((A A))) nat (u 0))",
        "(check bad (scope (i) ()) i nat)",
        "(check bad (lam i nat (papp (plam j nat zero) i)) (pi nat nat))",
        "(check bad (scope () ((p (path nat zero zero)))) (path i nat (papp p i) zero) (u 0))",
        "(check bad (lam nat nat zero) (pi nat nat))",
        "(check bad (lam 12 nat zero) (pi nat nat))",
        "(check bad (scope (i i) ()) zero nat)",
        "(check bad (scope () ((x nat) (x nat))) x nat)",
    ] {
        assert!(source::run(source).is_err(), "accepted {source}");
    }
}
