//! Adjust the right endpoint of a composition filler using a given path.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{cons, dim, papp, path, u, v};
use crate::cubical::engine::restricted_frontend::{RestrictedProducer, system};
use crate::cubical::engine::term::{Result, Sexp, atom, call};
use crate::cubical::engine::transport_frontend::transport_at;

pub fn to_pathp_line() -> Sexp {
    // h,d,c,Q,B,A. Outer j, inner composition direction k.
    let fill = call(
        "comp",
        [
            papp(v(3), call("meet", [dim(1), dim(0)])),
            Face::End(0, false).quote(),
            v(2),
            v(2),
        ],
    );
    let tube = system(&[
        (Face::End(1, false), v(2)),
        (Face::End(1, true), papp(v(0), dim(0))),
    ]);
    call(
        "plam",
        [call(
            "comp",
            [
                papp(v(3), dim(1)),
                Face::End(0, false).or(Face::End(0, true)).quote(),
                tube,
                fill,
            ],
        )],
    )
}
pub fn to_pathp_type(l: usize) -> Sexp {
    let hty = path(v(3), transport_at(v(2), v(1)), v(0));
    let result = path(papp(v(3), dim(0)), v(2), v(1));
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
                            call("pi", [v(2), call("pi", [v(2), call("pi", [hty, result])])]),
                        ],
                    ),
                ],
            ),
        ],
    )
}
pub fn to_pathp_context(l: usize) -> Sexp {
    let gab = cons(u(l), cons(u(l), atom("nil")));
    let gq = cons(path(u(l), v(1), v(0)), gab);
    let gc = cons(v(2), gq);
    let gd = cons(v(2), gc);
    cons(path(v(3), transport_at(v(2), v(1)), v(0)), gd)
}
pub fn to_pathp_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    let term = (0..6).fold(to_pathp_line(), |t, _| call("lam", [t]));
    let id = p.export_has(0, &atom("nil"), &term, &to_pathp_type(0))?;
    p.f.path.p.result("closed-to-pathp", id);
    let g = to_pathp_context(0);
    for (name, r, out, ty) in [
        ("to-pathp-left", "i0", v(2), v(5)),
        ("to-pathp-right", "i1", v(1), v(4)),
    ] {
        let id = p.equality(
            0,
            &g,
            &Face::True,
            &papp(to_pathp_line(), atom(r)),
            &out,
            &ty,
        )?;
        p.f.path.p.result(name, id);
    }
    Ok(p)
}
