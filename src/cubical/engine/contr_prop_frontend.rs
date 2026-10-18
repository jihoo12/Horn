//! Any two witnesses of contractibility are connected by an explicit square.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::glue_fiber_frontend::extend_contr;
use crate::cubical::engine::path_frontend::{Op, dim, papp, path, u, v};
use crate::cubical::engine::restricted_frontend::{RestrictedProducer, system};
use crate::cubical::engine::term::{Result, Sexp, atom, call};

fn app(f: Sexp, a: Sexp) -> Sexp {
    call("app", [f, a])
}
fn fst(t: Sexp) -> Sexp {
    call("fst", [t])
}
fn snd(t: Sexp) -> Sexp {
    call("snd", [t])
}
// Context d,c,X. The output is a path from c to d in Contr X.
pub fn contr_prop_line(p: &mut RestrictedProducer) -> Result<Sexp> {
    let centers = papp(app(snd(v(1)), fst(v(0))), dim(0));
    // Below lambda x and path i: x,d,c,X; dimension i,j.
    let boundary = Face::End(1, false)
        .or(Face::End(1, true))
        .or(Face::End(0, false))
        .or(Face::End(0, true));
    let partial = system(&[
        (Face::End(1, false), papp(app(snd(v(2)), v(0)), dim(0))),
        (Face::End(1, true), papp(app(snd(v(1)), v(0)), dim(0))),
        (Face::End(0, false), papp(app(snd(v(2)), fst(v(1))), dim(1))),
        (Face::End(0, true), v(0)),
    ]);
    let square = extend_contr(p, &v(3), &v(2), &boundary, &partial)?;
    let contraction = call("lam", [call("plam", [square])]);
    Ok(call("plam", [call("pair", [centers, contraction])]))
}
pub fn contr_prop_type(p: &mut RestrictedProducer, l: usize) -> Result<Sexp> {
    let (c, _) = p.contr_type(&v(0))?;
    let c1 = p.f.path.transform(&c, &Op::Shift(0))?.0;
    let c2 = p.f.path.transform(&c1, &Op::Shift(0))?.0;
    let family = p.f.path.transform(&c2, &Op::DShift(0))?.0;
    Ok(call(
        "pi",
        [
            u(l),
            call("pi", [c, call("pi", [c1, path(family, v(1), v(0))])]),
        ],
    ))
}
pub fn contr_prop_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    let line = contr_prop_line(&mut p)?;
    let term = (0..3).fold(line, |t, _| call("lam", [t]));
    let ty = contr_prop_type(&mut p, 0)?;
    let id = p.export_has(0, &atom("nil"), &term, &ty)?;
    p.f.path
        .p
        .result("closed-contractibility-is-proposition", id);
    Ok(p)
}
