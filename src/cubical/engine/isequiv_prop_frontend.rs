//! Pointwise contraction uniqueness gives a path between isEquiv witnesses.
use crate::cubical::engine::contr_prop_frontend::{contr_prop_line, contr_prop_type};
use crate::cubical::engine::path_frontend::{Op, dim, papp, path, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::sexp::{Result, Sexp, atom, call};

pub fn isequiv_prop_line(p: &mut RestrictedProducer, l: usize) -> Result<Sexp> {
    // Under y and path direction: y,d,c,f,B,A.
    let (fiber, _) = p.fiber_type(&v(5), &v(4), &v(3), &v(0))?;
    let ty = contr_prop_type(p, l)?;
    let term = (0..3).fold(contr_prop_line(p)?, |t, _| call("lam", [t]));
    let lemma = call("ann", [term, ty]);
    let cy = call("app", [v(2), v(0)]);
    let dy = call("app", [v(1), v(0)]);
    let applied = [fiber, cy, dy]
        .into_iter()
        .fold(lemma, |t, a| call("app", [t, a]));
    Ok(call("plam", [call("lam", [papp(applied, dim(0))])]))
}
pub fn isequiv_prop_type(p: &mut RestrictedProducer, l: usize) -> Result<Sexp> {
    let (c, _) = p.is_equiv_type(&v(2), &v(1), &v(0))?;
    let c1 = p.f.path.transform(&c, &Op::Shift(0))?.0;
    let c2 = p.f.path.transform(&c1, &Op::Shift(0))?.0;
    let family = p.f.path.transform(&c2, &Op::DShift(0))?.0;
    let result = path(family, v(1), v(0));
    Ok(call(
        "pi",
        [
            u(l),
            call(
                "pi",
                [
                    u(l),
                    call(
                        "pi",
                        [
                            call("pi", [v(1), v(1)]),
                            call("pi", [c, call("pi", [c1, result])]),
                        ],
                    ),
                ],
            ),
        ],
    ))
}
pub fn isequiv_prop_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    let term = (0..5).fold(isequiv_prop_line(&mut p, 0)?, |t, _| call("lam", [t]));
    let ty = isequiv_prop_type(&mut p, 0)?;
    let id = p.export_has(0, &atom("nil"), &term, &ty)?;
    p.f.path.p.result("closed-is-equiv-is-proposition", id);
    Ok(p)
}
