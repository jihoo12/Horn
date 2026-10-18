//! Univalence in the deep syntax at U₀: the canonical map from paths to
//! equivalences is itself an equivalence,
//!
//! ```text
//! Π A B:U₀. Equiv (Path U₀ A B) (Equiv A B)
//! ```
//!
//! with forward function `λP. canonical A B P`. The evidence applies the
//! closed isoToIsEquiv lemma to the inverse `λe. ua A B e` and the two inverse
//! laws. No univalence, inverse, or isomorphism rule is added.
//!
//! The lemma's hypotheses mention `f (g y)` and `g (f x)`. Both inverse laws
//! are therefore proved at exactly those redex types, so no conversion is
//! needed where they are passed:
//!
//! - the section applies extensionality to the redex `fwd (bwd e)` and the
//!   uaβ homotopy;
//! - the retraction is the Glue square of the second inverse, whose i=0 face
//!   is compared with `bwd (fwd P)`.
//!
//! As for the second inverse, everything is proved for the canonical-map
//! evidence `c` and the constant-equivalence path `w` as variables, then
//! applied to their closed proofs. The function component then becomes
//! exactly `canonical_map_at`.
use crate::cubical::engine::canonical_map_frontend::{apply, canonical_map_at, evidence_type};
use crate::cubical::engine::constant_equiv_frontend::constant_equiv_line;
use crate::cubical::engine::equiv_ext_frontend::{equiv_ext_line, equiv_ext_type};
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::iso_equiv_frontend::{iso_equiv_term, iso_equiv_type};
use crate::cubical::engine::path_frontend::{Op, cons, path, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::cubical::engine::ua_beta_frontend::{beta_term, beta_type};
use crate::cubical::engine::ua_eta_frontend::{canonical_with, constant_equiv_type, evidence, square};
use crate::cubical::engine::ua_frontend::{ua_term, ua_type};
use crate::cubical::engine::term::{Result, Sexp, atom, call};

/// `Equiv (Path U₀ A B) (Equiv A B)` in a context starting B, A.
pub fn statement(p: &mut RestrictedProducer) -> Result<Sexp> {
    let (equivs, _) = p.equiv_type(&v(1), &v(0))?;
    Ok(p.equiv_type(&path(u(0), v(1), v(0)), &equivs)?.0)
}

/// `Π A B:U₀. Equiv (Path U₀ A B) (Equiv A B)`.
pub fn univalence_type(p: &mut RestrictedProducer) -> Result<Sexp> {
    Ok(call("pi", [u(0), call("pi", [u(0), statement(p)?])]))
}

/// `λP. canonical A B P` with evidence `c`, in context B, A, w, c.
pub fn forward(p: &mut RestrictedProducer) -> Result<Sexp> {
    Ok(call(
        "lam",
        [canonical_with(p, &v(4), &v(2), &v(1), &v(0))?],
    ))
}

/// `λe. ua A B e` in context B, A, ...
pub fn backward(p: &mut RestrictedProducer) -> Result<Sexp> {
    let ua = call("ann", [ua_term(), ua_type(p, 0)?]);
    Ok(call("lam", [apply(ua, [v(2), v(1), v(0)])]))
}

fn shifted(p: &mut RestrictedProducer, t: &Sexp) -> Result<Sexp> {
    Ok(p.f.path.transform(t, &Op::Shift(0))?.0)
}

/// `λe. ext A B (fwd (bwd e)) e (λx. uaβ A B e x)`.
pub fn section(p: &mut RestrictedProducer, fwd: &Sexp, bwd: &Sexp) -> Result<Sexp> {
    let ext = (0..5).fold(equiv_ext_line(p, 0)?, |t, _| call("lam", [t]));
    let ext = call("ann", [ext, equiv_ext_type(p, 0)?]);
    let beta = call("ann", [beta_term(), beta_type(p, 0)?]);
    // Under λe: e, B, A.
    let (fwd, bwd) = (shifted(p, fwd)?, shifted(p, bwd)?);
    let redex = call("app", [fwd, call("app", [bwd, v(0)])]);
    // Under λx: x, e, B, A.
    let homotopy = call("lam", [apply(beta, [v(3), v(2), v(1), v(0)])]);
    Ok(call(
        "lam",
        [apply(ext, [v(2), v(1), redex, v(0), homotopy])],
    ))
}

/// The isEquiv evidence of the forward map, for variables c and w, in
/// context B, A, w, c.
pub fn evidence_body(p: &mut RestrictedProducer) -> Result<Sexp> {
    let fwd = forward(p)?;
    let bwd = backward(p)?;
    let section = section(p, &fwd, &bwd)?;
    // Under λP: P, B, A, w, c, the square's own context.
    let retraction = call("lam", [square(p)?]);
    let (equivs, _) = p.equiv_type(&v(1), &v(0))?;
    let iso = call("ann", [iso_equiv_term(p, 1, 0)?, iso_equiv_type(p, 1, 0)?]);
    let args = [
        path(u(0), v(1), v(0)),
        equivs,
        fwd,
        bwd,
        section,
        retraction,
    ];
    Ok(apply(iso, args))
}

/// `isEquiv (λP. canonical A B P)` with evidence c, in context B, A, w, c.
pub fn evidence_statement(p: &mut RestrictedProducer) -> Result<Sexp> {
    let fwd = forward(p)?;
    let (equivs, _) = p.equiv_type(&v(1), &v(0))?;
    Ok(p.is_equiv_type(&path(u(0), v(1), v(0)), &equivs, &fwd)?.0)
}

/// `λP. canonical A B P` with the closed evidence, in context B, A.
pub fn canonical_function(p: &mut RestrictedProducer) -> Result<Sexp> {
    Ok(call("lam", [canonical_map_at(p, 0, &v(2), &v(1), &v(0))?]))
}

/// `λA B. (λP. canonical A B P, lemma evidence w A B)`. The function component
/// sits directly in the pair, so projecting it needs only two β steps on
/// variables; the lemma, for variables c and w, supplies the evidence.
pub fn univalence_term(p: &mut RestrictedProducer) -> Result<Sexp> {
    let lemma = (0..4).fold(evidence_body(p)?, |t, _| call("lam", [t]));
    let over_ab = call("pi", [u(0), call("pi", [u(0), evidence_statement(p)?])]);
    let lemma_ty = call(
        "pi",
        [
            evidence_type(p, 0)?,
            call("pi", [constant_equiv_type(p)?, over_ab]),
        ],
    );
    let (w, _) = constant_equiv_line(p, 0)?;
    let lemma = call("ann", [lemma, lemma_ty]);
    let proof = apply(lemma, [evidence(p)?, call("lam", [w]), v(1), v(0)]);
    let body = call("pair", [canonical_function(p)?, proof]);
    Ok(call("lam", [call("lam", [body])]))
}

pub fn deep_univalence_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    p.f.path.p.archive_judgments();
    p.reuse_restricted_typings();
    p.f.path.memoize_transformations();
    p.reuse_certified_checks();
    p.strengthen_typings();
    // The closed proofs applied last are checked first. The lemma's own
    // hypothesis types revisit the same contexts, and the producer's typing
    // cache would otherwise steer the evidence's search the wrong way.
    let nil = atom("nil");
    let evidence_ty = evidence_type(&mut p, 0)?;
    let ev = evidence(&mut p)?;
    p.check(0, &nil, &Face::True, &ev, &evidence_ty)?;
    let (w, _) = constant_equiv_line(&mut p, 0)?;
    let open_w_ty = constant_equiv_type(&mut p)?;
    let (w_ty, _) = p.f.path.transform(&open_w_ty, &Op::Subst(0, ev))?;
    p.check(0, &nil, &Face::True, &call("lam", [w]), &w_ty)?;
    let term = univalence_term(&mut p)?;
    let ty = univalence_type(&mut p)?;
    let id = p.export_has(0, &atom("nil"), &term, &ty)?;
    p.f.path.p.result("closed-deep-univalence", id);
    // Its function component is the canonical map, in context B, A.
    let g = cons(u(0), cons(u(0), nil));
    let applied = call("fst", [apply(call("ann", [term, ty]), [v(1), v(0)])]);
    let canonical = canonical_function(&mut p)?;
    let (equivs, _) = p.equiv_type(&v(2), &v(1))?;
    let maps = call("pi", [path(u(0), v(1), v(0)), equivs]);
    let id = p.equality(0, &g, &Face::True, &applied, &canonical, &maps)?;
    p.f.path
        .p
        .result("deep-univalence-function-is-canonical", id);
    Ok(p)
}
