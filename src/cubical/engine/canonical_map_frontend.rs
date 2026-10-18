//! A canonical transport map whose equivalence evidence stays explicitly typed.
use crate::cubical::engine::homotopy_frontend::{homotopy_body, homotopy_type};
use crate::cubical::engine::path_frontend::{Op, path, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::cubical::engine::transport_equiv_frontend::{transport_function, transport_homotopy, transported_equiv};
use crate::cubical::engine::transport_frontend::transport_at;
use crate::sexp::{Result, Sexp, atom, call};

pub fn apply(f: Sexp, args: impl IntoIterator<Item = Sexp>) -> Sexp {
    args.into_iter().fold(f, |t, a| call("app", [t, a]))
}
pub fn evidence_term(p: &mut RestrictedProducer, l: usize) -> Result<Sexp> {
    let hty = homotopy_type(p, l)?;
    let hom = (0..5).fold(homotopy_body(p)?, |t, _| call("lam", [t]));
    let hom = call("ann", [hom, hty]);
    let e = transported_equiv(p, 0)?;
    let h = transport_homotopy(p)?;
    let body = apply(hom, [v(2), v(1), transport_function(), e, h]);
    Ok((0..3).fold(body, |t, _| call("lam", [t])))
}
pub fn evidence_type(p: &mut RestrictedProducer, l: usize) -> Result<Sexp> {
    let (property, _) = p.is_equiv_type(&v(2), &v(1), &transport_function())?;
    Ok(call(
        "pi",
        [
            u(l),
            call("pi", [u(l), call("pi", [path(u(l), v(1), v(0)), property])]),
        ],
    ))
}
pub fn canonical_map_at(
    p: &mut RestrictedProducer,
    l: usize,
    a: &Sexp,
    b: &Sexp,
    line: &Sexp,
) -> Result<Sexp> {
    let line_x = p.f.path.transform(line, &Op::Shift(0))?.0;
    let f = call("lam", [transport_at(line_x, v(0))]);
    let lemma = call("ann", [evidence_term(p, l)?, evidence_type(p, l)?]);
    let evidence = apply(lemma, [a.clone(), b.clone(), line.clone()]);
    let (et, _) = p.equiv_type(a, b)?;
    Ok(call("ann", [call("pair", [f, evidence]), et]))
}
pub fn canonical_map_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    p.f.path.p.archive_judgments();
    p.reuse_restricted_typings();
    let body = canonical_map_at(&mut p, 0, &v(2), &v(1), &v(0))?;
    let term = (0..3).fold(body.clone(), |t, _| call("lam", [t]));
    let ty = crate::cubical::engine::transport_equiv_frontend::transport_equiv_type(&mut p, 0)?;
    let id = p.export_has(0, &atom("nil"), &term, &ty)?;
    p.f.path.p.result("closed-canonical-transport-map", id);
    let g = crate::cubical::engine::transport_equiv_frontend::transport_equiv_context(0);
    let id = p.equality(
        0,
        &g,
        &crate::cubical::engine::face_frontend::Face::True,
        &call("fst", [body]),
        &transport_function(),
        &call("pi", [v(2), v(2)]),
    )?;
    p.f.path.p.result("canonical-map-forward-is-transport", id);
    Ok(p)
}
