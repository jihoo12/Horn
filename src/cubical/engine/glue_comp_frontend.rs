//! Instances of Glue composition (`req.comp-glue`, CCHM 6.2).
//!
//! The equivalences are context variables, so every partial term is typed
//! without annotations:
//!
//! - Under a dimension j, `Glue A [j=0 ↦ (T, e)]` is constant in the
//!   composition dimension, so δ = ∀i.(j=0) = (j=0) is not empty and every
//!   part of the construction (pres, t₁′, the fiber extension) is used.
//! - With the face ft, composition in the Glue type must agree with
//!   composition in T, since the Glue type is then judgmentally T. This
//!   coherence is checked as a judgment.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{cons, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::cubical::engine::term::{Result, Sexp, atom, call};

/// e : Equiv T A, T, A, with b0 at the Glue type `face` gives at i0.
fn context(p: &mut RestrictedProducer, face: &Face) -> Result<Sexp> {
    // In context T, A: Equiv T A.
    let (equiv, _) = p.equiv_type(&v(0), &v(1))?;
    let base = cons(equiv, cons(u(0), cons(u(0), atom("nil"))));
    let glue0 = call("glue-type", [v(2), face.quote(), v(1), v(0)]);
    Ok(cons(glue0, base))
}

/// `comp^i (Glue A [face ↦ (T, e)]) [] b0` in context b0, e, T, A, where
/// `face_i` is the face as seen under the composition binder.
fn composition(face_i: &Face) -> Sexp {
    let family = call("glue-type", [v(3), face_i.quote(), v(2), v(1)]);
    call("comp", [family, atom("ff"), atom("zero"), v(0)])
}

pub fn glue_comp_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    p.f.path.p.archive_judgments();
    p.reuse_restricted_typings();
    p.f.path.memoize_transformations();
    p.reuse_certified_checks();
    p.enable_composition_computation();
    // Under j: Glue A [j=0 ↦ (T, e)].
    let g = context(&mut p, &Face::End(0, false))?;
    let t = composition(&Face::End(1, false));
    let (_, id) = p.glue_composition(1, &g, &Face::True, &t)?;
    p.f.path.p.result("glue-composition-under-a-face", id);
    // Glue A [ft ↦ (T, e)] composes like T.
    let g = context(&mut p, &Face::True)?;
    let t = composition(&Face::True);
    let in_t = call("comp", [v(2), atom("ff"), atom("zero"), v(0)]);
    let id = p.equality(0, &g, &Face::True, &t, &in_t, &v(2))?;
    p.f.path
        .p
        .result("glue-composition-on-the-full-face-is-composition-in-t", id);
    Ok(p)
}
