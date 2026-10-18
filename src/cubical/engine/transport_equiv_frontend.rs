//! Canonical transport is an equivalence, using an explicit Equiv-family fill.
//! Only deep terms, composition, identity fibers, and homotopy transfer are used.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::homotopy_frontend::{homotopy_body, homotopy_type};
use crate::cubical::engine::identity_frontend::identity_core;
use crate::cubical::engine::path_frontend::{cons, dim, papp, path, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::cubical::engine::transport_frontend::transport_at;
use crate::cubical::engine::term::{Result, Sexp, atom, call};

// Context P,B,A with optional extra ordinary variables.
pub fn transported_equiv(p: &mut RestrictedProducer, offset: usize) -> Result<Sexp> {
    let (family, _) = p.equiv_type(&v(2 + offset), &papp(v(offset), dim(0)))?;
    Ok(call(
        "comp",
        [family, atom("ff"), atom("zero"), identity_core()],
    ))
}
// Context x,P,B,A. Outer direction r, inner composition direction k.
pub fn equivalence_fill(p: &mut RestrictedProducer) -> Result<Sexp> {
    let point = papp(v(1), call("meet", [dim(1), dim(0)]));
    let (family, _) = p.equiv_type(&v(3), &point)?;
    Ok(call(
        "comp",
        [
            family,
            Face::End(0, false).quote(),
            identity_core(),
            identity_core(),
        ],
    ))
}
pub fn transport_graph(p: &mut RestrictedProducer) -> Result<Sexp> {
    Ok(call(
        "plam",
        [call("app", [call("fst", [equivalence_fill(p)?]), v(0)])],
    ))
}
pub fn transport_homotopy(p: &mut RestrictedProducer) -> Result<Sexp> {
    let graph = transport_graph(p)?;
    Ok(call(
        "lam",
        [call(
            "plam",
            [call(
                "comp",
                [
                    papp(v(1), dim(0)),
                    Face::End(0, true).quote(),
                    papp(graph, dim(0)),
                    v(0),
                ],
            )],
        )],
    ))
}
pub fn transport_function() -> Sexp {
    call("lam", [transport_at(v(1), v(0))])
}
pub fn transport_equiv_body(p: &mut RestrictedProducer, l: usize) -> Result<Sexp> {
    let lemma_ty = homotopy_type(p, l)?;
    let lemma = (0..5).fold(homotopy_body(p)?, |t, _| call("lam", [t]));
    let g = transport_equiv_context(l);
    // An annotation is checked, never used as an unchecked inference hint.
    p.check(0, &g, &Face::True, &lemma, &lemma_ty)?;
    let e = transported_equiv(p, 0)?;
    let h = transport_homotopy(p)?;
    let f = transport_function();
    let evidence = [v(2), v(1), f.clone(), e, h]
        .into_iter()
        .fold(lemma, |t, a| call("app", [t, a]));
    Ok(call("pair", [f, evidence]))
}
pub fn transport_equiv_context(l: usize) -> Sexp {
    cons(path(u(l), v(1), v(0)), cons(u(l), cons(u(l), atom("nil"))))
}
pub fn transport_equiv_type(p: &mut RestrictedProducer, l: usize) -> Result<Sexp> {
    let (e, _) = p.equiv_type(&v(2), &v(1))?;
    Ok(call(
        "pi",
        [
            u(l),
            call("pi", [u(l), call("pi", [path(u(l), v(1), v(0)), e])]),
        ],
    ))
}
pub fn transport_equiv_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    let g = transport_equiv_context(0);
    let gx = cons(v(2), g.clone());
    let e = transported_equiv(&mut p, 1)?;
    let graph = transport_graph(&mut p)?;
    let gt = path(
        papp(v(1), dim(0)),
        v(0),
        call("app", [call("fst", [e]), v(0)]),
    );
    let id = p.check(0, &gx, &Face::True, &graph, &gt)?;
    p.f.path.p.result("transport-equivalence-graph", id);
    let body = transport_equiv_body(&mut p, 0)?;
    let ty = transport_equiv_type(&mut p, 0)?;
    let term = (0..3).fold(body.clone(), |t, _| call("lam", [t]));
    let id = p.export_has(0, &atom("nil"), &term, &ty)?;
    p.f.path.p.result("closed-path-to-equiv", id);
    let id = p.equality(
        0,
        &g,
        &Face::True,
        &call("fst", [body]),
        &transport_function(),
        &call("pi", [v(2), v(2)]),
    )?;
    p.f.path
        .p
        .result("path-to-equiv-forward-is-canonical-transport", id);
    Ok(p)
}
