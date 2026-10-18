//! Specialize the derived Glue fiber contraction to the actual ua systems.
use crate::cubical::engine::glue_fiber_frontend::{glue_fiber_extension, unglue_function};
use crate::cubical::engine::path_frontend::{cons, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::cubical::engine::ua_frontend::ua_family;
use crate::sexp::{Result, atom, call};

pub fn ua_unglue_demo() -> Result<RestrictedProducer> {
    use crate::cubical::engine::face_frontend::Face;
    use crate::cubical::engine::glue_fiber_frontend::glue_fiber_contraction;
    use crate::cubical::engine::identity_frontend::identity_core;
    use crate::cubical::engine::path_frontend::Op;
    use crate::cubical::engine::restricted_frontend::system;
    let mut p = RestrictedProducer::default();
    p.f.path.p.archive_judgments();
    p.reuse_restricted_typings();
    p.reuse_closed_annotations();
    // First abstract the endpoint equivalence. Its identity contraction is
    // checked once as an argument, instead of re-elaborated in every cube.
    // Context I,e,B,A; I : Equiv B B.
    let boundary = Face::End(0, false).or(Face::End(0, true));
    let partial = system(&[(Face::End(0, false), v(3)), (Face::End(0, true), v(2))]);
    let equivs = system(&[(Face::End(0, false), v(1)), (Face::End(0, true), v(0))]);
    let gt = call("glue-type", [v(2), boundary.quote(), partial, equivs]);
    let gt_a = p.f.path.transform(&gt, &Op::Shift(0))?.0;
    let contraction = glue_fiber_contraction(&mut p, &gt_a, &v(0))?;
    let proof_body = call("lam", [contraction]);
    let generic = (0..4).fold(proof_body, |t, _| call("lam", [t]));
    let (et, _) = p.equiv_type(&v(1), &v(0))?;
    let (it, _) = p.equiv_type(&v(1), &v(1))?;
    let (property, _) = p.is_equiv_type(&gt, &v(2), &unglue_function())?;
    let generic_type = call(
        "pi",
        [
            u(0),
            call(
                "pi",
                [u(0), call("pi", [et.clone(), call("pi", [it, property])])],
            ),
        ],
    );
    let lemma = call("ann", [generic, generic_type]);
    let evidence = [v(2), v(1), v(0), identity_core()]
        .into_iter()
        .fold(lemma, |t, a| call("app", [t, a]));
    let witness = call("pair", [unglue_function(), evidence]);
    let (eqv, _) = p.equiv_type(&ua_family(0), &v(1))?;
    let ty = call("pi", [u(0), call("pi", [u(0), call("pi", [et, eqv])])]);
    let term = (0..3).fold(witness, |t, _| call("lam", [t]));
    let id = p.export_has(1, &atom("nil"), &term, &ty)?;
    p.f.path.p.result("ua-unglue-equivalence", id);
    Ok(p)
}

pub fn ua_unglue_center_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    p.f.path.p.archive_judgments();
    p.reuse_restricted_typings();
    let (et, _) = p.equiv_type(&v(1), &v(0))?;
    let ge = cons(et, cons(u(0), cons(u(0), atom("nil"))));
    let g = cons(v(1), ge);
    let gt = ua_family(1);
    let (fiber, _) = p.fiber_type(&gt, &v(2), &unglue_function(), &v(0))?;
    let center = glue_fiber_extension(
        &mut p,
        &gt,
        &crate::cubical::engine::face_frontend::Face::False,
        &atom("zero"),
        &v(0),
    )?;
    let id = p.check(1, &g, &crate::cubical::engine::face_frontend::Face::True, &center, &fiber)?;
    p.f.path.p.result("ua-unglue-fiber-center", id);
    Ok(p)
}
