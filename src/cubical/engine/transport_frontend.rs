//! Dependent path -> path from transport to its right endpoint.
//! The transport is still a composition term; this is a derived path equality,
//! not a type-directed Glue/universe normalization algorithm.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{cons, dim, papp, path, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::sexp::{Result, Sexp, atom, call};

pub fn transport_at(line: Sexp, x: Sexp) -> Sexp {
    call("comp", [papp(line, dim(0)), atom("ff"), atom("zero"), x])
}
pub fn from_pathp_line() -> Sexp {
    // Context p,y,x,P,B,A. Outer dimension j; composition binds i.
    call(
        "plam",
        [call(
            "comp",
            [
                papp(v(3), dim(0)),
                Face::End(0, true).quote(),
                papp(v(0), dim(0)),
                v(2),
            ],
        )],
    )
}
pub fn from_pathp_term() -> Sexp {
    (0..6).fold(from_pathp_line(), |t, _| call("lam", [t]))
}
pub fn from_pathp_type(l: usize) -> Sexp {
    let result = path(v(4), transport_at(v(3), v(2)), v(1));
    let pty = path(papp(v(2), dim(0)), v(1), v(0));
    call(
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
                            path(u(l), v(1), v(0)),
                            call("pi", [v(2), call("pi", [v(2), call("pi", [pty, result])])]),
                        ],
                    ),
                ],
            ),
        ],
    )
}
pub fn transport_context(l: usize) -> Sexp {
    let gab = cons(u(l), cons(u(l), atom("nil")));
    let gp = cons(path(u(l), v(1), v(0)), gab);
    let gx = cons(v(2), gp);
    let gy = cons(v(2), gx);
    cons(path(papp(v(2), dim(0)), v(1), v(0)), gy)
}
pub fn transport_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    let id = p.export_has(0, &atom("nil"), &from_pathp_term(), &from_pathp_type(0))?;
    p.f.path.p.result("closed-from-pathp", id);
    let g = transport_context(0);
    for (name, r, target) in [
        ("from-pathp-left", "i0", transport_at(v(3), v(2))),
        ("from-pathp-right", "i1", v(1)),
    ] {
        let id = p.equality(
            0,
            &g,
            &Face::True,
            &papp(from_pathp_line(), atom(r)),
            &target,
            &v(4),
        )?;
        p.f.path.p.result(name, id);
    }
    Ok(p)
}
