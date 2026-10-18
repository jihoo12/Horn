//! First ua inverse: `canonical (ua e) = e` as a path of equivalences.
//!
//! Equivalence extensionality reduces it to a pointwise homotopy between
//! the forward functions. The forward function of the canonical map is
//! transport along `ua e`, so the derived uaβ path supplies the homotopy:
//!
//! ```text
//! equiv-ext A B (canonical A B (ua A B e)) e (λx. uaβ A B e x)
//! ```
//!
//! No inverse law, ua-beta rule, or extensionality rule is added. The closed
//! extensionality and uaβ proofs appear annotated, so applying them takes
//! their types from the annotations and their typing is checked once. The
//! producer types each subterm in the shortest context it needs and lifts it
//! with the existing structural rule `rhas.shift`; without that, the Glue
//! line was re-typed at every binder of the expanded isEquiv type.
use crate::cubical::engine::canonical_map_frontend::{apply, canonical_map_at};
use crate::cubical::engine::equiv_ext_frontend::{equiv_ext_line, equiv_ext_type};
use crate::cubical::engine::path_frontend::{path, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::cubical::engine::ua_beta_frontend::{beta_term, beta_type};
use crate::cubical::engine::ua_frontend::{ua_term, ua_type};
use crate::sexp::{Result, Sexp, atom, call};

/// `ua A B e` with A, B, e at v2, v1, v0.
pub fn ua_e(p: &mut RestrictedProducer) -> Result<Sexp> {
    let ua = call("ann", [ua_term(), ua_type(p, 0)?]);
    Ok(apply(ua, [v(2), v(1), v(0)]))
}

/// `canonical A B (ua A B e)` with A, B, e at v2, v1, v0.
pub fn canonical_ua(p: &mut RestrictedProducer) -> Result<Sexp> {
    let line = ua_e(p)?;
    canonical_map_at(p, 0, &v(2), &v(1), &line)
}

/// `Π A B:U₀. Π e:Equiv A B. Path (Equiv A B) (canonical A B (ua A B e)) e`.
pub fn canonical_ua_type(p: &mut RestrictedProducer) -> Result<Sexp> {
    let (et, _) = p.equiv_type(&v(2), &v(1))?;
    let statement = path(et, canonical_ua(p)?, v(0));
    let (et, _) = p.equiv_type(&v(1), &v(0))?;
    Ok(call(
        "pi",
        [u(0), call("pi", [u(0), call("pi", [et, statement])])],
    ))
}

pub fn canonical_ua_term(p: &mut RestrictedProducer) -> Result<Sexp> {
    let ext = (0..5).fold(equiv_ext_line(p, 0)?, |t, _| call("lam", [t]));
    let ext = call("ann", [ext, equiv_ext_type(p, 0)?]);
    let beta = call("ann", [beta_term(), beta_type(p, 0)?]);
    // Under λx: x, e, B, A at v0..v3.
    let homotopy = call("lam", [apply(beta, [v(3), v(2), v(1), v(0)])]);
    let body = apply(ext, [v(2), v(1), canonical_ua(p)?, v(0), homotopy]);
    Ok((0..3).fold(body, |t, _| call("lam", [t])))
}

pub fn canonical_ua_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    p.f.path.p.archive_judgments();
    p.reuse_restricted_typings();
    p.f.path.memoize_transformations();
    p.reuse_certified_checks();
    p.strengthen_typings();
    let term = canonical_ua_term(&mut p)?;
    let ty = canonical_ua_type(&mut p)?;
    let id = p.export_has(0, &atom("nil"), &term, &ty)?;
    p.f.path.p.result("closed-canonical-ua", id);
    Ok(p)
}
