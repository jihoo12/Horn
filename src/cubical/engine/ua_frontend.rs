//! Closed Glue-based forward map. Full computational univalence is unfinished.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::identity_frontend::identity_core;
use crate::cubical::engine::path_frontend::{cons, path, u, v};
use crate::cubical::engine::restricted_frontend::{RestrictedProducer, system};
use crate::sexp::{Result, Sexp, atom, call};

pub fn ua_family(offset: usize) -> Sexp {
    // Under <i>, ordinary context is e : Equiv A B, B : U_l, A : U_l.
    let phi = Face::End(0, false).or(Face::End(0, true));
    let types = system(&[
        (Face::End(0, false), v(2 + offset)),
        (Face::End(0, true), v(1 + offset)),
    ]);
    let equivs = system(&[
        (Face::End(0, false), v(offset)),
        (Face::End(0, true), identity_core()),
    ]);
    call("glue-type", [v(1 + offset), phi.quote(), types, equivs])
}
pub fn ua_line() -> Sexp {
    call("plam", [ua_family(0)])
}
pub fn ua_term() -> Sexp {
    call("lam", [call("lam", [call("lam", [ua_line()])])])
}
pub fn ua_type(p: &mut RestrictedProducer, l: usize) -> Result<Sexp> {
    let (eqv, _) = p.equiv_type(&v(1), &v(0))?;
    Ok(call(
        "pi",
        [
            u(l),
            call("pi", [u(l), call("pi", [eqv, path(u(l), v(2), v(1))])]),
        ],
    ))
}
pub fn check_ua(p: &mut RestrictedProducer, l: usize) -> Result<usize> {
    let ty = ua_type(p, l)?;
    p.export_has(0, &atom("nil"), &ua_term(), &ty)
}
pub fn ua_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    let id = check_ua(&mut p, 0)?;
    p.f.path.p.result("closed-ua", id);
    let gab = cons(u(0), cons(u(0), atom("nil")));
    let (eqv, _) = p.equiv_type(&v(1), &v(0))?;
    let g = cons(eqv, gab);
    for (name, r, out) in [("ua-left", "i0", v(2)), ("ua-right", "i1", v(1))] {
        let app = call("papp", [ua_line(), atom(r)]);
        let id = p.equality(0, &g, &Face::True, &app, &out, &u(0))?;
        p.f.path.p.result(name, id);
    }
    Ok(p)
}
