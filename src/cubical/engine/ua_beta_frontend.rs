//! Derived path transport(ua e) x = e x, with an explicit composition filler.
//! No ua-beta axiom: this is an ordinary term in the deep object language.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{dim, papp, path, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::cubical::engine::transport_frontend::transport_at;
use crate::cubical::engine::ua_frontend::ua_family;
use crate::cubical::engine::ua_graph_frontend::{graph_context, graph_line, mapped_x};
use crate::cubical::engine::term::{Result, Sexp, atom, call};

pub fn ua_at_x() -> Sexp {
    call("plam", [ua_family(1)])
}
pub fn beta_line() -> Sexp {
    call(
        "plam",
        [call(
            "comp",
            [
                papp(ua_at_x(), dim(0)),
                Face::End(0, true).quote(),
                papp(graph_line(), dim(0)),
                v(0),
            ],
        )],
    )
}
pub fn beta_term() -> Sexp {
    (0..4).fold(beta_line(), |t, _| call("lam", [t]))
}
pub fn beta_type(p: &mut RestrictedProducer, l: usize) -> Result<Sexp> {
    let (eqv, _) = p.equiv_type(&v(1), &v(0))?;
    let result = path(v(2), transport_at(ua_at_x(), v(0)), mapped_x());
    Ok(call(
        "pi",
        [
            u(l),
            call("pi", [u(l), call("pi", [eqv, call("pi", [v(2), result])])]),
        ],
    ))
}
pub fn beta_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    let ty = beta_type(&mut p, 0)?;
    let id = p.export_has(0, &atom("nil"), &beta_term(), &ty)?;
    p.f.path.p.result("closed-ua-beta", id);
    let g = graph_context(&mut p, 0)?;
    for (name, r, out) in [
        ("ua-beta-left", "i0", transport_at(ua_at_x(), v(0))),
        ("ua-beta-right", "i1", mapped_x()),
    ] {
        let id = p.equality(0, &g, &Face::True, &papp(beta_line(), atom(r)), &out, &v(2))?;
        p.f.path.p.result(name, id);
    }
    Ok(p)
}
