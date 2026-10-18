//! Transport along ua computes judgmentally, by Glue composition:
//!
//! ```text
//! x:A, e:Equiv A B, B, A ⊢ transport^i (ua e i) x ≡ transport^k B (transport^i B (e x)) : B
//! ```
//!
//! Without judgmental regularity the two constant transports in B remain, as
//! in CCHM. The family is the actual `ua_family`; its identity equivalence is
//! an unannotated pair, so the producer keeps reducts annotated with the types
//! they were reduced at.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::v;
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::cubical::engine::ua_frontend::ua_family;
use crate::cubical::engine::ua_graph_frontend::{graph_context, mapped_x};
use crate::sexp::{Result, Sexp, atom, call};

/// `transport^i (ua e i) x`, with the Glue family written directly.
pub fn transport_ua() -> Sexp {
    call("comp", [ua_family(1), atom("ff"), atom("zero"), v(0)])
}

/// `transport^i B y` for B at v2 in context x, e, B, A.
fn transport_b(y: Sexp) -> Sexp {
    call("comp", [v(2), atom("ff"), atom("zero"), y])
}

pub fn computed() -> Sexp {
    transport_b(transport_b(mapped_x()))
}

pub fn ua_transport_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    p.f.path.p.archive_judgments();
    p.reuse_restricted_typings();
    p.f.path.memoize_transformations();
    p.reuse_certified_checks();
    p.strengthen_typings();
    p.keep_reduct_types();
    p.enable_composition_computation();
    let g = graph_context(&mut p, 0)?;
    let id = p.equality(0, &g, &Face::True, &transport_ua(), &computed(), &v(2))?;
    p.f.path.p.result("transport-along-ua-computes", id);
    Ok(p)
}
