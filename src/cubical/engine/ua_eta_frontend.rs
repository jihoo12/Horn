//! Second ua inverse: `ua (canonical P) = P` as a path of paths, by the Glue
//! square of CCHM Appendix B, Lemma 25(3). It is an ordinary deep term; no
//! inverse law, univalence rule, or judgmental regularity is added.
//!
//! Under dimensions i (outer) and j (inner) the square is
//!
//! ```text
//! Glue B [ i=1 ↦ (P j, canonical (P j) B (⟨k⟩ P (j ∨ k)))
//!        , j=0 ↦ (A,   canonical A B P)
//!        , j=1 ↦ (B,   w B (~i)) ]
//! ```
//!
//! where `w : Π X:U₀. Path (Equiv X X) (canonical X X ⟨_⟩X) identity` is the
//! constant canonical equivalence path. At i=0 the j=1 equivalence is the
//! identity, so the face is `ua (canonical P)`; at i=1 the Glue is attached
//! everywhere and computes to `P j`. The two equivalences that meet at
//! i=1, j=1 are related by `w`'s endpoint, not identified judgmentally.
//!
//! The square is proved for variables: `c`, the evidence that canonical
//! transport is an equivalence, and `w`. So the search never unfolds either
//! proof. The closed proofs are applied last; substituting them yields exactly
//! the terms `canonical_map_at` and `constant_equiv_line` build.
use crate::cubical::engine::canonical_map_frontend::{apply, evidence_term, evidence_type};
use crate::cubical::engine::constant_equiv_frontend::constant_equiv_line;
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::identity_frontend::identity_core;
use crate::cubical::engine::path_frontend::{Op, cons, dim, papp, path, u, v};
use crate::cubical::engine::restricted_frontend::{RestrictedProducer, system};
use crate::cubical::engine::transport_frontend::transport_at;
use crate::cubical::engine::ua_frontend::{ua_term, ua_type};
use crate::cubical::engine::term::{Result, Sexp, atom, call};

/// The canonical map of `line : Path U₀ a b` with evidence `c`. With the
/// closed evidence lemma for `c` and a line without free dimensions this is
/// `canonical_map_at`; the line is also lifted under the transport's
/// composition binder, so it may mention ambient dimensions.
pub fn canonical_with(
    p: &mut RestrictedProducer,
    c: &Sexp,
    a: &Sexp,
    b: &Sexp,
    line: &Sexp,
) -> Result<Sexp> {
    let line_x = p.f.path.transform(line, &Op::Shift(0))?.0;
    let line_k = p.f.path.transform(&line_x, &Op::DShift(0))?.0;
    let f = call("lam", [transport_at(line_k, v(0))]);
    let evidence = apply(c.clone(), [a.clone(), b.clone(), line.clone()]);
    let (et, _) = p.equiv_type(a, b)?;
    Ok(call("ann", [call("pair", [f, evidence]), et]))
}

pub fn evidence(p: &mut RestrictedProducer) -> Result<Sexp> {
    Ok(call("ann", [evidence_term(p, 0)?, evidence_type(p, 0)?]))
}

/// `Π X:U₀. Path (Equiv X X) (canonical X X ⟨_⟩X) identity` in context [c].
pub fn constant_equiv_type(p: &mut RestrictedProducer) -> Result<Sexp> {
    let line = call("ann", [call("plam", [v(0)]), path(u(0), v(0), v(0))]);
    let canonical = canonical_with(p, &v(1), &v(0), &v(0), &line)?;
    let (et, _) = p.equiv_type(&v(0), &v(0))?;
    let identity = call("ann", [identity_core(), et.clone()]);
    Ok(call("pi", [u(0), path(et, canonical, identity)]))
}

/// Square context: P (v0) : Path U₀ A B, B (v1), A (v2), w (v3), c (v4).
pub fn square_context(p: &mut RestrictedProducer) -> Result<Sexp> {
    let c = cons(evidence_type(p, 0)?, atom("nil"));
    let w = cons(constant_equiv_type(p)?, c);
    let ab = cons(u(0), cons(u(0), w));
    Ok(cons(path(u(0), v(1), v(0)), ab))
}

pub fn canonical_p(p: &mut RestrictedProducer) -> Result<Sexp> {
    canonical_with(p, &v(4), &v(2), &v(1), &v(0))
}

/// `⟨k⟩ P (j ∨ k) : Path U₀ (P j) B`, under dimensions i, j.
pub fn suffix_line() -> Sexp {
    let body = papp(v(0), call("join", [dim(1), dim(0)]));
    call(
        "ann",
        [call("plam", [body]), path(u(0), papp(v(0), dim(0)), v(1))],
    )
}

pub fn square_face() -> Face {
    Face::End(1, true)
        .or(Face::End(0, false))
        .or(Face::End(0, true))
}

pub fn square_glue(p: &mut RestrictedProducer) -> Result<Sexp> {
    let types = system(&[
        (Face::End(1, true), papp(v(0), dim(0))),
        (Face::End(0, false), v(2)),
        (Face::End(0, true), v(1)),
    ]);
    let suffix = canonical_with(p, &v(4), &papp(v(0), dim(0)), &v(1), &suffix_line())?;
    let constant = papp(call("app", [v(3), v(1)]), call("neg", [dim(1)]));
    let equivs = system(&[
        (Face::End(1, true), suffix),
        (Face::End(0, false), canonical_p(p)?),
        (Face::End(0, true), constant),
    ]);
    Ok(call(
        "glue-type",
        [v(1), square_face().quote(), types, equivs],
    ))
}

pub fn square(p: &mut RestrictedProducer) -> Result<Sexp> {
    Ok(call("plam", [call("plam", [square_glue(p)?])]))
}

/// `Path (Path U₀ A B) (ua A B (canonical A B P)) P` with A, B, P at v2, v1,
/// v0 and the evidence at `c`.
pub fn statement(p: &mut RestrictedProducer, c: &Sexp) -> Result<Sexp> {
    let ua = call("ann", [ua_term(), ua_type(p, 0)?]);
    let canonical = canonical_with(p, c, &v(2), &v(1), &v(0))?;
    let left = apply(ua, [v(2), v(1), canonical]);
    Ok(path(path(u(0), v(2), v(1)), left, v(0)))
}

/// `Π A B:U₀. Π P:Path U₀ A B. body`.
pub fn over_paths(body: Sexp) -> Sexp {
    let paths = call("pi", [path(u(0), v(1), v(0)), body]);
    call("pi", [u(0), call("pi", [u(0), paths])])
}

/// The closed theorem's type, with the closed evidence lemma.
pub fn ua_eta_type(p: &mut RestrictedProducer) -> Result<Sexp> {
    let evidence = evidence(p)?;
    Ok(over_paths(statement(p, &evidence)?))
}

/// The square abstracted over c and w, applied to their closed proofs.
pub fn ua_eta_term(p: &mut RestrictedProducer) -> Result<Sexp> {
    let lemma = (0..5).fold(square(p)?, |t, _| call("lam", [t]));
    let body = over_paths(statement(p, &v(4))?);
    let lemma_ty = call(
        "pi",
        [
            evidence_type(p, 0)?,
            call("pi", [constant_equiv_type(p)?, body]),
        ],
    );
    let (w, _) = constant_equiv_line(p, 0)?;
    let lemma = call("ann", [lemma, lemma_ty]);
    Ok(apply(lemma, [evidence(p)?, call("lam", [w])]))
}

fn configure(p: &mut RestrictedProducer) {
    p.f.path.p.archive_judgments();
    p.reuse_restricted_typings();
    p.f.path.memoize_transformations();
    p.reuse_certified_checks();
}

/// Only the square, for variables c and w: much smaller than the theorem.
pub fn square_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    configure(&mut p);
    let g = square_context(&mut p)?;
    let t = square(&mut p)?;
    let ty = statement(&mut p, &v(4))?;
    let id = p.check(0, &g, &Face::True, &t, &ty)?;
    p.f.path.p.result("ua-eta-square", id);
    Ok(p)
}

pub fn ua_eta_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    configure(&mut p);
    let term = ua_eta_term(&mut p)?;
    let ty = ua_eta_type(&mut p)?;
    let id = p.export_has(0, &atom("nil"), &term, &ty)?;
    p.f.path.p.result("closed-ua-eta", id);
    Ok(p)
}
