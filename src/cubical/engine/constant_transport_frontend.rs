//! Constant transport is homotopic to identity; no judgmental regularity axiom.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{cons, dim, papp, path, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::cubical::engine::transport_frontend::transport_at;
use crate::cubical::engine::term::{Result, Sexp, atom, call};

// Ordinary context x:A, A:U_l. The type A has no free dimensions.
pub fn constant_line(l: usize) -> Sexp {
    call("ann", [call("plam", [v(1)]), path(u(l), v(1), v(1))])
}
pub fn constant_transport_path(l: usize) -> Sexp {
    call(
        "plam",
        [call(
            "comp",
            [
                papp(constant_line(l), dim(0)),
                Face::End(0, true).quote(),
                v(0),
                v(0),
            ],
        )],
    )
}
pub fn constant_transport_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    for l in [0, 1] {
        let source = transport_at(constant_line(l), v(0));
        let ty = call(
            "pi",
            [u(l), call("pi", [v(0), path(v(1), source.clone(), v(0))])],
        );
        let term = call("lam", [call("lam", [constant_transport_path(l)])]);
        let id = p.export_has(0, &atom("nil"), &term, &ty)?;
        p.f.path
            .p
            .result(&format!("constant-transport-homotopy-level-{l}"), id);
        let g = cons(v(0), cons(u(l), atom("nil")));
        for (name, endpoint, out) in [("left", "i0", source), ("right", "i1", v(0))] {
            let id = p.equality(
                0,
                &g,
                &Face::True,
                &papp(constant_transport_path(l), atom(endpoint)),
                &out,
                &v(1),
            )?;
            p.f.path
                .p
                .result(&format!("constant-transport-{name}-level-{l}"), id);
        }
    }
    Ok(p)
}
