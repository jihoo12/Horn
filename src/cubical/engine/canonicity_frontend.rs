//! Canonicity of transport along ua, for a closed equivalence on bool:
//!
//! ```text
//! ⊢ transport^i (ua not i) btrue ≡ bfalse : bool
//! ```
//!
//! `not` is `λb. bif bool bfalse btrue b`; it is an equivalence by the closed
//! isoToIsEquiv lemma, applied to `not`, `not` and the inverse law proved by
//! the dependent eliminator. The ua family is the one of `ua_frontend`, at
//! A = B = bool. Evaluation runs through Glue composition and bool's
//! composition; nothing here is an oracle for the result.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::identity_frontend::identity_core;
use crate::cubical::engine::iso_equiv_frontend::{iso_equiv_term, iso_equiv_type};
use crate::cubical::engine::path_frontend::{path, v};
use crate::cubical::engine::restricted_frontend::{RestrictedProducer, system};
use crate::sexp::{Result, Sexp, atom, call};

fn app(f: Sexp, a: Sexp) -> Sexp {
    call("app", [f, a])
}
fn bool() -> Sexp {
    atom("bool")
}

/// `not : bool → bool`, annotated so that it can be inferred anywhere.
pub fn not() -> Sexp {
    let body = call("bif", [bool(), atom("bfalse"), atom("btrue"), v(0)]);
    call("ann", [call("lam", [body]), call("pi", [bool(), bool()])])
}

/// `λb. bif (λc. Path bool (not (not c)) c) refl refl b`.
pub fn not_involutive() -> Sexp {
    let motive = path(bool(), app(not(), app(not(), v(0))), v(0));
    let refl = |c: &str| call("plam", [atom(c)]);
    let body = call("bif", [motive, refl("btrue"), refl("bfalse"), v(0)]);
    call("lam", [body])
}

/// `(not, isoToIsEquiv bool bool not not inv inv) : Equiv bool bool`.
pub fn not_equivalence(p: &mut RestrictedProducer) -> Result<Sexp> {
    let lemma = call(
        "ann",
        [iso_equiv_term(p, 0, 0)?, iso_equiv_type(p, 0, 0)?],
    );
    let proof = [bool(), bool(), not(), not(), not_involutive(), not_involutive()]
        .into_iter()
        .fold(lemma, app);
    Ok(call("pair", [not(), proof]))
}

/// `ua e` at dimension 0, for a closed `e : Equiv A A`.
pub fn ua_family(a: &Sexp, e: &Sexp) -> Sexp {
    let phi = Face::End(0, false).or(Face::End(0, true));
    let types = system(&[(Face::End(0, false), a.clone()), (Face::End(0, true), a.clone())]);
    let equivs = system(&[
        (Face::End(0, false), e.clone()),
        (Face::End(0, true), identity_core()),
    ]);
    call("glue-type", [a.clone(), phi.quote(), types, equivs])
}

pub fn transport(family: Sexp, x: Sexp) -> Sexp {
    call("comp", [family, atom("ff"), atom("zero"), x])
}

pub fn producer() -> RestrictedProducer {
    let mut p = RestrictedProducer::default();
    p.f.path.p.archive_judgments();
    p.reuse_restricted_typings();
    p.f.path.memoize_transformations();
    p.reuse_certified_checks();
    p.strengthen_typings();
    p.keep_reduct_types();
    p.enable_composition_computation();
    p
}

/// The goals `transport (ua not) b ≡ not b` for both booleans.
pub fn canonicity_demo() -> Result<RestrictedProducer> {
    let mut p = producer();
    let nil = atom("nil");
    let e = not_equivalence(&mut p)?;
    let (et, _) = p.equiv_type(&bool(), &bool())?;
    let ei = p.check(0, &nil, &Face::True, &e, &et)?;
    p.f.path.p.result("not-is-an-equivalence", ei);
    let e = call("ann", [e, et]);
    for (name, x, out) in [
        ("transport-ua-not-true", "btrue", "bfalse"),
        ("transport-ua-not-false", "bfalse", "btrue"),
    ] {
        let t = transport(ua_family(&bool(), &e), atom(x));
        let id = p.equality(0, &nil, &Face::True, &t, &atom(out), &bool())?;
        p.f.path.p.result(name, id);
    }
    Ok(p)
}
