//! A closed dependent graph of ua, constructed by deep Glue introduction.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{cons, dim, papp, path, u, v};
use crate::cubical::engine::restricted_frontend::{RestrictedProducer, system};
use crate::cubical::engine::term::{Result, Sexp, atom, call};
use crate::cubical::engine::ua_frontend::ua_family;

// Context x:A, e:Equiv A B, B:U_l, A:U_l.
pub fn mapped_x() -> Sexp {
    call("app", [call("fst", [v(1)]), v(0)])
}
pub fn graph_body() -> Sexp {
    let partial = system(&[
        (Face::End(0, false), v(0)),
        (Face::End(0, true), mapped_x()),
    ]);
    call("glue", [ua_family(1), partial, mapped_x()])
}
pub fn graph_line() -> Sexp {
    call("plam", [graph_body()])
}
pub fn graph_term() -> Sexp {
    (0..4).fold(graph_line(), |t, _| call("lam", [t]))
}
pub fn graph_line_type() -> Sexp {
    let family = papp(call("plam", [ua_family(1)]), dim(0));
    path(family, v(0), mapped_x())
}
pub fn graph_type(p: &mut RestrictedProducer, l: usize) -> Result<Sexp> {
    let (eqv, _) = p.equiv_type(&v(1), &v(0))?;
    Ok(call(
        "pi",
        [
            u(l),
            call(
                "pi",
                [
                    u(l),
                    call("pi", [eqv, call("pi", [v(2), graph_line_type()])]),
                ],
            ),
        ],
    ))
}
pub fn graph_context(p: &mut RestrictedProducer, l: usize) -> Result<Sexp> {
    let gab = cons(u(l), cons(u(l), atom("nil")));
    let (eqv, _) = p.equiv_type(&v(1), &v(0))?;
    Ok(cons(v(2), cons(eqv, gab)))
}
pub fn graph_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    let ty = graph_type(&mut p, 0)?;
    let id = p.export_has(0, &atom("nil"), &graph_term(), &ty)?;
    p.f.path.p.result("closed-ua-graph", id);
    let g = graph_context(&mut p, 0)?;
    for (name, r, out, ty) in [
        ("graph-left", "i0", v(0), v(3)),
        ("graph-right", "i1", mapped_x(), v(2)),
    ] {
        let id = p.equality(0, &g, &Face::True, &papp(graph_line(), atom(r)), &out, &ty)?;
        p.f.path.p.result(name, id);
    }
    let id = p.equality(
        1,
        &g,
        &Face::True,
        &call("unglue", [graph_body()]),
        &mapped_x(),
        &v(2),
    )?;
    p.f.path.p.result("graph-unglue", id);
    Ok(p)
}
