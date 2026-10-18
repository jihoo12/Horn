//! A map with an inverse and both inverse laws is an equivalence, as a closed
//! deep term. This follows `isoToIsEquiv` and `lemIso` of the Cubical library
//! (Cubical.Foundations.Isomorphism): every fiber element is connected to
//! `(g y, s y)` by squares built from five explicit compositions. No
//! equivalence, isomorphism, or contractibility rule is added.
//!
//! Dimensions are de Bruijn indices. A two-dimensional body has free
//! dimensions i (dim 1) and j (dim 0); `inst` instantiates them through the
//! certified dimension substitution, which also substitutes faces.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{Op, dim, papp, path, u, v};
use crate::cubical::engine::restricted_frontend::{RestrictedProducer, system};
use crate::sexp::{Result, Sexp, atom, call};

fn app(f: Sexp, a: Sexp) -> Sexp {
    call("app", [f, a])
}
fn meet(a: Sexp, b: Sexp) -> Sexp {
    call("meet", [a, b])
}
fn neg(r: Sexp) -> Sexp {
    call("neg", [r])
}

// Ordinary context of the fiber lemma:
// p1, p0, x1, x0, y, t, s, g, f, Y, X at v0..v10.
const P1: usize = 0;
const P0: usize = 1;
const X1: usize = 2;
const X0: usize = 3;
const Y: usize = 4;
const T: usize = 5;
const S: usize = 6;
const G: usize = 7;
const F: usize = 8;
const TY: usize = 9;
const TX: usize = 10;

/// A body with free dimensions i (dim 1) and j (dim 0) at `ri`, `rj`, which
/// are intervals of the current context.
fn inst(p: &mut RestrictedProducer, body: &Sexp, ri: &Sexp, rj: &Sexp) -> Result<Sexp> {
    let rj = p.f.path.itransform(rj, &Op::DShift(0))?.0;
    let body = p.f.path.transform(body, &Op::DSubst(0, rj))?.0;
    Ok(p.f.path.transform(&body, &Op::DSubst(0, ri.clone()))?.0)
}

/// i=1 ∨ i=0 ∨ j=0, and with j=1 as well.
fn three_faces() -> Face {
    Face::End(1, true)
        .or(Face::End(1, false))
        .or(Face::End(0, false))
}
fn four_faces() -> Face {
    Face::End(1, true)
        .or(Face::End(1, false))
        .or(Face::End(0, true))
        .or(Face::End(0, false))
}

/// `fill i j = hfill (λk. [i=1 ↦ t x k, i=0 ↦ g y]) (g (p (~i))) j`.
/// Inside the tube, k is dim 0, j dim 1, and i dim 2.
fn fill(x: usize, q: usize) -> Sexp {
    let tube = system(&[
        (
            Face::End(2, true),
            papp(app(v(T), v(x)), meet(dim(0), dim(1))),
        ),
        (Face::End(2, false), app(v(G), v(Y))),
        (Face::End(1, false), app(v(G), papp(v(q), neg(dim(2))))),
    ]);
    let base = app(v(G), papp(v(q), neg(dim(1))));
    call("comp", [v(TX), three_faces().quote(), tube, base])
}

/// `fill2 i j = hfill (λk. [i=1 ↦ fill1 k 1, i=0 ↦ fill0 k 1]) (g y) j`.
fn fill2(p: &mut RestrictedProducer) -> Result<Sexp> {
    let k_j = meet(dim(0), dim(1));
    let tube = system(&[
        (
            Face::End(2, true),
            inst(p, &fill(X1, P1), &k_j, &atom("i1"))?,
        ),
        (
            Face::End(2, false),
            inst(p, &fill(X0, P0), &k_j, &atom("i1"))?,
        ),
        (Face::End(1, false), app(v(G), v(Y))),
    ]);
    Ok(call(
        "comp",
        [v(TX), three_faces().quote(), tube, app(v(G), v(Y))],
    ))
}

/// `p i = fill2 i 1`, the path from x0 to x1.
fn along(p: &mut RestrictedProducer, ri: &Sexp) -> Result<Sexp> {
    let body = fill2(p)?;
    inst(p, &body, ri, &atom("i1"))
}

/// `sq i j = hcomp (λk. [i=1 ↦ fill1 j (~k), i=0 ↦ fill0 j (~k),
/// j=1 ↦ t (p i) (~k), j=0 ↦ g y]) (fill2 i j)`.
fn square(p: &mut RestrictedProducer) -> Result<Sexp> {
    let back = neg(dim(0));
    let tube = system(&[
        (Face::End(2, true), inst(p, &fill(X1, P1), &dim(1), &back)?),
        (Face::End(2, false), inst(p, &fill(X0, P0), &dim(1), &back)?),
        (
            Face::End(1, true),
            papp(app(v(T), along(p, &dim(2))?), back.clone()),
        ),
        (Face::End(1, false), app(v(G), v(Y))),
    ]);
    Ok(call("comp", [v(TX), four_faces().quote(), tube, fill2(p)?]))
}

/// `sq1 i j = hcomp (λk. [i=1 ↦ s (p1 (~j)) k, i=0 ↦ s (p0 (~j)) k,
/// j=1 ↦ s (f (p i)) k, j=0 ↦ s y k]) (f (sq i j))`.
fn square1(p: &mut RestrictedProducer) -> Result<Sexp> {
    let section = |t: Sexp| papp(app(v(S), t), dim(0));
    let tube = system(&[
        (Face::End(2, true), section(papp(v(P1), neg(dim(1))))),
        (Face::End(2, false), section(papp(v(P0), neg(dim(1))))),
        (Face::End(1, true), section(app(v(F), along(p, &dim(2))?))),
        (Face::End(1, false), section(v(Y))),
    ]);
    Ok(call(
        "comp",
        [v(TY), four_faces().quote(), tube, app(v(F), square(p)?)],
    ))
}

/// `⟨i⟩ (p i, ⟨j⟩ sq1 i (~j)) : Path (fiber f y) (x0, p0) (x1, p1)`.
pub fn fiber_line(p: &mut RestrictedProducer) -> Result<Sexp> {
    let first = along(p, &dim(0))?;
    let body = square1(p)?;
    let second = call("plam", [inst(p, &body, &dim(1), &neg(dim(0)))?]);
    Ok(call("plam", [call("pair", [first, second])]))
}

/// The hypotheses X:U_m, Y:U_n, f, g, s, t as nested Π types around `body`.
fn over_iso(m: usize, n: usize, body: Sexp) -> Sexp {
    // Context Y, X: f : X → Y.
    let f = call("pi", [v(1), v(1)]);
    // Context f, Y, X: g : Y → X.
    let g = call("pi", [v(1), v(3)]);
    // Context g, f, Y, X: s : Π y. Path Y (f (g y)) y.
    let s = call("pi", [v(2), path(v(3), app(v(2), app(v(1), v(0))), v(0))]);
    // Context s, g, f, Y, X: t : Π x. Path X (g (f x)) x.
    let t = call("pi", [v(4), path(v(5), app(v(2), app(v(3), v(0))), v(0))]);
    let body = call("pi", [t, body]);
    let body = call("pi", [s, body]);
    let body = call("pi", [g, body]);
    let body = call("pi", [f, body]);
    call("pi", [u(m), call("pi", [u(n), body])])
}

/// `Π X Y f g s t (y:Y) (x0 x1:X) (p0 : Path Y (f x0) y) (p1 : Path Y (f x1) y).
/// Path (fiber f y) (x0, p0) (x1, p1)`.
pub fn fiber_line_type(p: &mut RestrictedProducer, m: usize, n: usize) -> Result<Sexp> {
    let (fiber, _) = p.fiber_type(&v(TX), &v(TY), &v(F), &v(Y))?;
    let result = path(
        fiber,
        call("pair", [v(X0), v(P0)]),
        call("pair", [v(X1), v(P1)]),
    );
    // Contexts, innermost last: [.., Y, X] then y, x0, x1, p0, p1.
    let p1 = path(v(8), app(v(7), v(1)), v(3));
    let p0 = path(v(7), app(v(6), v(1)), v(2));
    let body = call("pi", [p0, call("pi", [p1, result])]);
    let body = call("pi", [v(6), call("pi", [v(7), body])]);
    Ok(over_iso(m, n, call("pi", [v(4), body])))
}

/// `Π X Y f g s t. isEquiv f`.
pub fn iso_equiv_type(p: &mut RestrictedProducer, m: usize, n: usize) -> Result<Sexp> {
    let (is_equiv, _) = p.is_equiv_type(&v(5), &v(4), &v(3))?;
    Ok(over_iso(m, n, is_equiv))
}

/// `λX Y f g s t y. ((g y, s y), λz. lemIso y (g y) (fst z) (s y) (snd z))`.
pub fn iso_equiv_term(p: &mut RestrictedProducer, m: usize, n: usize) -> Result<Sexp> {
    let lemma = (0..11).fold(fiber_line(p)?, |t, _| call("lam", [t]));
    let lemma = call("ann", [lemma, fiber_line_type(p, m, n)?]);
    // Under λy λz: z, y, t, s, g, f, Y, X at v0..v7.
    let args = [
        v(7),
        v(6),
        v(5),
        v(4),
        v(3),
        v(2),
        v(1),
        app(v(4), v(1)),
        call("fst", [v(0)]),
        app(v(3), v(1)),
        call("snd", [v(0)]),
    ];
    let contraction = call("lam", [args.into_iter().fold(lemma, app)]);
    // Under λy: y, t, s, g, f at v0..v4.
    let center = call("pair", [app(v(3), v(0)), app(v(2), v(0))]);
    let body = call("lam", [call("pair", [center, contraction])]);
    Ok((0..6).fold(body, |t, _| call("lam", [t])))
}

pub fn iso_equiv_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    p.f.path.p.archive_judgments();
    p.reuse_restricted_typings();
    p.f.path.memoize_transformations();
    p.reuse_certified_checks();
    p.strengthen_typings();
    let term = iso_equiv_term(&mut p, 0, 0)?;
    let ty = iso_equiv_type(&mut p, 0, 0)?;
    let id = p.export_has(0, &atom("nil"), &term, &ty)?;
    p.f.path.p.result("closed-iso-is-equivalence", id);
    Ok(p)
}
