//! Transport a genuine isEquiv witness along a pointwise homotopy.
//! The property family is expanded into Pi/Sigma/Path; no isEquiv oracle.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{cons, dim, papp, path, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::sexp::{Result, Sexp, atom, call};

// Under the composition direction j, context h,e,f,B,A.
pub fn homotopy_function() -> Sexp {
    call(
        "lam",
        [papp(call("app", [v(1), v(0)]), call("neg", [dim(0)]))],
    )
}
pub fn homotopy_body(p: &mut RestrictedProducer) -> Result<Sexp> {
    let (property, _) = p.is_equiv_type(&v(4), &v(3), &homotopy_function())?;
    Ok(call(
        "comp",
        [property, atom("ff"), atom("zero"), call("snd", [v(1)])],
    ))
}
pub fn homotopy_type(p: &mut RestrictedProducer, l: usize) -> Result<Sexp> {
    // Before e: context f,B,A.
    let (eqv, _) = p.equiv_type(&v(2), &v(1))?;
    // Before h: context e,f,B,A; the h argument binds x.
    let hx = path(
        v(3),
        call("app", [v(2), v(0)]),
        call("app", [call("fst", [v(1)]), v(0)]),
    );
    let hty = call("pi", [v(3), hx]);
    let (result, _) = p.is_equiv_type(&v(4), &v(3), &v(2))?;
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
                            call("pi", [eqv, call("pi", [hty, result])]),
                        ],
                    ),
                ],
            ),
        ],
    ))
}
pub fn homotopy_context(p: &mut RestrictedProducer, l: usize) -> Result<Sexp> {
    let gab = cons(u(l), cons(u(l), atom("nil")));
    let gf = cons(call("pi", [v(1), v(1)]), gab);
    let (eqv, _) = p.equiv_type(&v(2), &v(1))?;
    let ge = cons(eqv, gf);
    let hty = call(
        "pi",
        [
            v(3),
            path(
                v(3),
                call("app", [v(2), v(0)]),
                call("app", [call("fst", [v(1)]), v(0)]),
            ),
        ],
    );
    Ok(cons(hty, ge))
}
pub fn homotopy_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    let ty = homotopy_type(&mut p, 0)?;
    let body = homotopy_body(&mut p)?;
    let term = (0..5).fold(body.clone(), |t, _| call("lam", [t]));
    let id = p.export_has(0, &atom("nil"), &term, &ty)?;
    p.f.path.p.result("closed-homotopy-is-equiv", id);
    let g = homotopy_context(&mut p, 0)?;
    let (result, _) = p.is_equiv_type(&v(4), &v(3), &v(2))?;
    let id = p.check(0, &g, &Face::True, &body, &result)?;
    p.f.path.p.result("homotopy-is-equiv-instance", id);
    Ok(p)
}
