//! A pointwise homotopy of equivalence functions gives a path of equivalences.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::isequiv_prop_frontend::{isequiv_prop_line, isequiv_prop_type};
use crate::cubical::engine::path_frontend::{Op, dim, papp, path, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::cubical::engine::to_pathp_frontend::{to_pathp_line, to_pathp_type};
use crate::cubical::engine::transport_frontend::transport_at;
use crate::cubical::engine::term::{Result, Sexp, atom, call};

fn fst(t: Sexp) -> Sexp {
    call("fst", [t])
}
fn snd(t: Sexp) -> Sexp {
    call("snd", [t])
}
fn apply(f: Sexp, args: impl IntoIterator<Item = Sexp>) -> Sexp {
    args.into_iter().fold(f, |t, a| call("app", [t, a]))
}
// h,e,d,B,A, h x : Path B (fst d x) (fst e x).
pub fn equiv_ext_line(p: &mut RestrictedProducer, l: usize) -> Result<Sexp> {
    let fbody = call("lam", [papp(call("app", [v(1), v(0)]), dim(0))]);
    let function_type = call("pi", [v(4), v(4)]);
    let fline_type = path(function_type, fst(v(2)), fst(v(1)));
    let fline = call("ann", [call("plam", [fbody.clone()]), fline_type]);
    let (property, _) = p.is_equiv_type(&v(4), &v(3), &fbody)?;
    let q = call("plam", [property]);
    let (a, _) = p.is_equiv_type(&v(4), &v(3), &fst(v(2)))?;
    let (b, _) = p.is_equiv_type(&v(4), &v(3), &fst(v(1)))?;
    let c = snd(v(2));
    let d = snd(v(1));
    let prop_term = (0..5).fold(isequiv_prop_line(p, l)?, |t, _| call("lam", [t]));
    let prop_ty = isequiv_prop_type(p, l)?;
    let right_path = apply(
        call("ann", [prop_term, prop_ty]),
        [
            v(4),
            v(3),
            fst(v(1)),
            transport_at(q.clone(), c.clone()),
            d.clone(),
        ],
    );
    let bridge = (0..6).fold(to_pathp_line(), |t, _| call("lam", [t]));
    let bridge_ty = to_pathp_type(l);
    let dependent = apply(
        call("ann", [bridge, bridge_ty]),
        [a, b, q, c, d, right_path],
    );
    let fline_j = p.f.path.transform(&fline, &Op::DShift(0))?.0;
    let dependent_j = p.f.path.transform(&dependent, &Op::DShift(0))?.0;
    Ok(call(
        "plam",
        [call(
            "pair",
            [papp(fline_j, dim(0)), papp(dependent_j, dim(0))],
        )],
    ))
}
pub fn equiv_ext_type(p: &mut RestrictedProducer, l: usize) -> Result<Sexp> {
    let (et, _) = p.equiv_type(&v(1), &v(0))?;
    let et1 = p.f.path.transform(&et, &Op::Shift(0))?.0;
    let h = call(
        "pi",
        [
            v(3),
            path(
                v(3),
                call("app", [fst(v(2)), v(0)]),
                call("app", [fst(v(1)), v(0)]),
            ),
        ],
    );
    let (family, _) = p.equiv_type(&v(4), &v(3))?;
    let result = path(family, v(2), v(1));
    Ok(call(
        "pi",
        [
            u(l),
            call(
                "pi",
                [
                    u(l),
                    call("pi", [et, call("pi", [et1, call("pi", [h, result])])]),
                ],
            ),
        ],
    ))
}
pub fn equiv_ext_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    p.f.path.p.archive_judgments();
    p.reuse_restricted_typings();
    let ty = equiv_ext_type(&mut p, 0)?;
    let term = (0..5).fold(equiv_ext_line(&mut p, 0)?, |t, _| call("lam", [t]));
    let id = p.export_has(0, &atom("nil"), &term, &ty)?;
    p.f.path.p.result("closed-equivalence-extensionality", id);
    // No face-restricted assumptions are exported.
    p.ctx(0, &atom("nil"), &Face::True)?;
    Ok(p)
}
