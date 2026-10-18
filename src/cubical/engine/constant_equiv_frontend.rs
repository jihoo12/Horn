//! Canonical transport along a constant type path is connected to identity.
//! All equivalence evidence and extensionality are expanded deep terms.
use crate::cubical::engine::canonical_map_frontend::{apply, canonical_map_at};
use crate::cubical::engine::constant_transport_frontend::{constant_line, constant_transport_path};
use crate::cubical::engine::equiv_ext_frontend::{equiv_ext_line, equiv_ext_type};
use crate::cubical::engine::identity_frontend::identity_core;
use crate::cubical::engine::path_frontend::{Op, path, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::cubical::engine::term::{Result, Sexp, atom, call};

// Context A:U_l. constant_line expects an extra x, so lower its ordinary index.
pub fn constant_equiv_endpoints(p: &mut RestrictedProducer, l: usize) -> Result<(Sexp, Sexp)> {
    let line =
        p.f.path
            .transform(&constant_line(l), &Op::Subst(0, atom("zero")))?
            .0;
    let canonical = canonical_map_at(p, l, &v(0), &v(0), &line)?;
    let (et, _) = p.equiv_type(&v(0), &v(0))?;
    Ok((canonical, call("ann", [identity_core(), et])))
}
pub fn constant_equiv_line(p: &mut RestrictedProducer, l: usize) -> Result<(Sexp, Sexp)> {
    let (canonical, identity) = constant_equiv_endpoints(p, l)?;
    let (et, _) = p.equiv_type(&v(0), &v(0))?;
    let ty = path(et, canonical.clone(), identity.clone());
    let ext = (0..5).fold(equiv_ext_line(p, l)?, |t, _| call("lam", [t]));
    let ext = call("ann", [ext, equiv_ext_type(p, l)?]);
    let homotopy = call("lam", [constant_transport_path(l)]);
    Ok((apply(ext, [v(0), v(0), canonical, identity, homotopy]), ty))
}
pub fn constant_equiv_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    p.f.path.p.archive_judgments();
    p.reuse_restricted_typings();
    p.f.path.memoize_transformations();
    p.reuse_certified_checks();
    let (body, ty) = constant_equiv_line(&mut p, 0)?;
    let term = call("lam", [body]);
    let ty = call("pi", [u(0), ty]);
    let id = p.export_has(0, &atom("nil"), &term, &ty)?;
    p.f.path
        .p
        .result("constant-canonical-equivalence-to-identity", id);
    Ok(p)
}
