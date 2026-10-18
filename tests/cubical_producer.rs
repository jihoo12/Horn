use horn::cubical::{
    ast::{Interval as I, Term as T},
    producer::{self, Judgment, Request},
};
use horn::kernel::Theory;

fn bx(t: T) -> Box<T> {
    Box::new(t)
}
fn pi(a: T, b: T) -> T {
    T::Pi(bx(a), bx(b))
}
fn lam(a: T, b: T) -> T {
    T::Lam(bx(a), bx(b))
}
fn app(f: T, a: T) -> T {
    T::App(bx(f), bx(a))
}
fn path(a: T, b: T, c: T) -> T {
    T::Path(bx(a), bx(b), bx(c))
}
fn plam(a: T, b: T) -> T {
    T::PathLam(bx(a), bx(b))
}
fn papp(p: T, r: I) -> T {
    T::PathApp(bx(p), r)
}
fn has(name: &str, term: T, ty: T) -> Request {
    Request {
        name: name.into(),
        dimensions: 0,
        context: vec![],
        judgment: Judgment::Has { term, ty },
    }
}
fn eq(name: &str, left: T, right: T, ty: T) -> Request {
    Request {
        name: name.into(),
        dimensions: 0,
        context: vec![],
        judgment: Judgment::Equal { left, right, ty },
    }
}
fn accepts(requests: &[Request]) -> producer::Generated {
    let out = producer::produce(requests).unwrap();
    let checked = Theory::parse(producer::THEORY)
        .unwrap()
        .check(&out.goals, &out.proof)
        .unwrap();
    assert_eq!(checked.goals, requests.len());
    out
}

#[test]
fn fresh_dependent_functions_at_multiple_universe_levels() {
    for l in 0..4 {
        let id = lam(T::Universe(l), lam(T::Var(0), T::Var(0)));
        let ty = pi(T::Universe(l), pi(T::Var(0), T::Var(1)));
        accepts(&[has("identity", id, ty)]);
    }
    let id = lam(T::Universe(0), lam(T::Var(0), T::Var(0)));
    accepts(&[has(
        "apply-polymorphic-identity",
        app(app(id, T::Nat), T::Zero),
        T::Nat,
    )]);
}

#[test]
fn fresh_beta_and_path_computation_are_ground_certificates() {
    let id = lam(T::Nat, T::Var(0));
    let p = plam(T::Nat, T::Zero);
    let mut at_dimension = eq(
        "path-at-dimension",
        papp(p.clone(), I::Var(0)),
        T::Zero,
        T::Nat,
    );
    at_dimension.dimensions = 1;
    let out = accepts(&[
        eq("beta", app(id.clone(), T::Zero), T::Zero, T::Nat),
        eq("beta-symmetric", T::Zero, app(id, T::Zero), T::Nat),
        has("constant-path", p.clone(), path(T::Nat, T::Zero, T::Zero)),
        eq("path-at-zero", papp(p.clone(), I::Zero), T::Zero, T::Nat),
        eq("path-at-one", papp(p, I::One), T::Zero, T::Nat),
        at_dimension,
    ]);
    assert!(out.proof.contains("eq.beta"));
    assert!(out.proof.contains("eq.pbeta"));
}

#[test]
fn open_paths_use_checked_endpoint_rules_and_shifted_contexts() {
    for (r, rule) in [(I::Zero, "eq.p0"), (I::One, "eq.p1")] {
        let mut request = eq("endpoint", papp(T::Var(0), r), T::Zero, T::Nat);
        request.context = vec![path(T::Nat, T::Zero, T::Zero)];
        let out = accepts(&[request]);
        assert!(out.proof.contains(rule));
    }
    let mut request = has(
        "open-constant-path",
        plam(T::Nat, T::Var(0)),
        path(T::Nat, T::Var(0), T::Var(0)),
    );
    request.context = vec![T::Nat];
    accepts(&[request]);
}

#[test]
fn ordinary_substitution_crossing_dimension_binders_lifts_replacement() {
    // In context p : Path Nat 0 0 and dimension i, substitute p @ i
    // across the path binder in λx:Nat. <j> x. The replacement's i must
    // become dim 1 under j, then return to dim 0 after path application.
    let p = path(T::Nat, T::Zero, T::Zero);
    let replacement = papp(T::Var(0), I::Var(0));
    let f = lam(T::Nat, plam(T::Nat, T::Var(0)));
    let result = plam(T::Nat, papp(T::Var(0), I::Var(1)));
    let ty = path(T::Nat, replacement.clone(), replacement.clone());
    let mut request = eq("capture-avoiding", app(f, replacement), result, ty);
    request.dimensions = 1;
    request.context = vec![p];
    let out = accepts(&[request]);
    assert!(out.proof.contains("subst.plam"));
    assert!(out.proof.contains("dshift.papp"));
    let mut ordinary = eq(
        "ordinary-capture",
        app(lam(T::Nat, lam(T::Nat, T::Var(1))), T::Var(0)),
        lam(T::Nat, T::Var(1)),
        pi(T::Nat, T::Nat),
    );
    ordinary.context = vec![T::Nat];
    accepts(&[ordinary]);
}

#[test]
fn dimension_substitution_crosses_nested_path_binders() {
    let inner = plam(T::Nat, T::Zero);
    let outer = plam(path(T::Nat, T::Zero, T::Zero), inner.clone());
    let mut request = eq(
        "nested-path",
        papp(outer, I::Var(0)),
        inner,
        path(T::Nat, T::Zero, T::Zero),
    );
    request.dimensions = 1;
    let out = accepts(&[request]);
    assert!(out.proof.contains("dsubst.plam"));
    assert!(out.proof.contains("ishift.dim.ge"));
    // Substitution for an outer dimension crosses the inner path binder.
    // Its replacement must refer to the free dimension, not the inner one.
    let p = path(T::Nat, T::Zero, T::Zero);
    let endpoint = papp(T::Var(0), I::Var(0));
    let family = path(T::Nat, endpoint.clone(), endpoint);
    let inner = plam(T::Nat, papp(T::Var(0), I::Var(1)));
    let outer = plam(family.clone(), inner.clone());
    let mut request = eq(
        "nested-dimension-capture",
        papp(outer, I::Var(0)),
        inner,
        family,
    );
    request.dimensions = 1;
    request.context = vec![p];
    accepts(&[request]);
}

#[test]
fn dimension_dependent_contexts_are_shifted_before_path_introduction() {
    let universe_path = path(T::Universe(0), T::Nat, T::Nat);
    let a = papp(T::Var(0), I::Var(0));
    let shifted_family = papp(T::Var(1), I::Var(1));
    let mut request = has(
        "dependent-context-path",
        plam(shifted_family.clone(), T::Var(0)),
        path(shifted_family, T::Var(0), T::Var(0)),
    );
    request.dimensions = 1;
    request.context = vec![universe_path, a];
    let out = accepts(&[request]);
    assert!(out.proof.contains("dshiftctx.cons"));
    assert!(out.proof.contains("ishift.dim.ge"));
}

#[test]
fn invalid_typing_scope_and_goals_are_rejected() {
    let cases = [
        has("self-universe", T::Universe(0), T::Universe(0)),
        has("free-variable", T::Var(0), T::Nat),
        has("bad-application", app(T::Zero, T::Zero), T::Nat),
        has("bad-argument", app(lam(T::Nat, T::Var(0)), T::Nat), T::Nat),
        has(
            "free-dimension",
            papp(plam(T::Nat, T::Zero), I::Var(0)),
            T::Nat,
        ),
        has(
            "wrong-endpoint",
            plam(T::Nat, T::Zero),
            path(T::Nat, T::Zero, T::Nat),
        ),
        has("invalid-context", T::Zero, T::Nat),
    ];
    for mut request in cases {
        if request.name == "invalid-context" {
            request.context = vec![T::Zero];
        }
        assert!(
            producer::produce(&[request.clone()]).is_err(),
            "accepted {}",
            request.name
        );
    }
    let out = accepts(&[has("identity", lam(T::Nat, T::Var(0)), pi(T::Nat, T::Nat))]);
    let forged = out.goals.replace("(pi nat nat)", "(pi nat (u z))");
    assert!(
        Theory::parse(producer::THEORY)
            .unwrap()
            .check(&forged, &out.proof)
            .is_err()
    );
    let forged_proof = out.proof.replace("type.lam", "invented.axiom");
    assert!(
        Theory::parse(producer::THEORY)
            .unwrap()
            .check(&out.goals, &forged_proof)
            .is_err()
    );
}
