//! Glue fiber extension built from the partial equivalence's contractions.
//! Face parameters are macro parameters, never new trusted inference rules.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{Op, cons, dim, papp, u, v};
use crate::cubical::engine::restricted_frontend::{RestrictedProducer, system};
use crate::cubical::engine::term::{Result, Sexp, atom, call};

fn lift(p: &mut RestrictedProducer, t: &Sexp) -> Result<Sexp> {
    Ok(p.f.path.transform(t, &Op::DShift(0))?.0)
}
fn lift_face(p: &mut RestrictedProducer, f: &Face) -> Result<Face> {
    Face::parse(&p.f.path.ftransform(&f.quote(), &Op::DShift(0))?.0)
}
fn projection(s: &str, t: &Sexp) -> Sexp {
    call(s, [t.clone()])
}

// Extend a partial element w of a contractible type X along psi.
pub fn extend_contr(
    p: &mut RestrictedProducer,
    x: &Sexp,
    contraction: &Sexp,
    psi: &Face,
    w: &Sexp,
) -> Result<Sexp> {
    let x2 = lift(p, x)?;
    let c2 = lift(p, contraction)?;
    let w2 = lift(p, w)?;
    let tube = papp(call("app", [projection("snd", &c2), w2]), dim(0));
    Ok(call(
        "comp",
        [x2, psi.quote(), tube, projection("fst", contraction)],
    ))
}
// Extend w : fiber(unglue,a) on psi to a total element of that same fiber.
pub fn glue_fiber_extension(
    p: &mut RestrictedProducer,
    gt: &Sexp,
    psi: &Face,
    w: &Sexp,
    a: &Sexp,
) -> Result<Sexp> {
    let Sexp::List(xs) = gt else {
        return Err("expected Glue type".into());
    };
    if xs.len() != 5 || xs[0] != atom("glue-type") {
        return Err("expected Glue type".into());
    }
    let (base, phi, partial, e) = (&xs[1], Face::parse(&xs[2])?, &xs[3], &xs[4]);
    // A system of equivalences can have different branch domain types.
    // Its expected dependent Equiv type must accompany every shifted use.
    let annotated_e = if matches!(e, Sexp::List(es) if es.first() == Some(&atom("system"))) {
        let (et, _) = p.equiv_type(partial, base)?;
        // A nonempty fiber tube can select and project a single branch.
        // Preserve the expected type on that selected erased introduction too.
        fn annotate_branches(s: &Sexp, ty: &Sexp) -> Result<Sexp> {
            if *s == atom("snil") {
                return Ok(s.clone());
            }
            let Sexp::List(xs) = s else {
                return Err("invalid equivalence system".into());
            };
            if xs.len() != 4 || xs[0] != atom("side") {
                return Err("invalid equivalence system".into());
            }
            Ok(call(
                "side",
                [
                    xs[1].clone(),
                    call("ann", [xs[2].clone(), ty.clone()]),
                    annotate_branches(&xs[3], ty)?,
                ],
            ))
        }
        let annotated = if psi.normal() == Face::False {
            e.clone()
        } else {
            let Sexp::List(xs) = e else { unreachable!() };
            call("system", [annotate_branches(&xs[1], &et)?])
        };
        call("ann", [annotated, et])
    } else {
        e.clone()
    };
    let e = &annotated_e;
    let (unglue_fiber, _) = p.fiber_type(gt, base, &unglue_function(), a)?;
    let annotated = if psi.normal() == Face::False {
        w.clone()
    } else {
        call("ann", [w.clone(), unglue_fiber])
    };
    let w = &annotated;
    let (fiber, _) = p.fiber_type(partial, base, &projection("fst", e), a)?;
    let contraction = call("app", [projection("snd", e), a.clone()]);
    let pair = call("pair", [projection("fst", w), projection("snd", w)]);
    let ext = extend_contr(p, &fiber, &contraction, psi, &pair)?;
    let t = projection("fst", &ext);
    let pp = projection("snd", &ext);
    let q = projection("snd", w);
    let phi2 = lift_face(p, &phi)?;
    let psi2 = lift_face(p, psi)?;
    let base2 = lift(p, base)?;
    let pp2 = lift(p, &pp)?;
    let q2 = lift(p, &q)?;
    let a2 = lift(p, a)?;
    let tube = system(&[
        (phi2.clone(), papp(pp2.clone(), call("neg", [dim(0)]))),
        (psi2.clone(), papp(q2.clone(), call("neg", [dim(0)]))),
    ]);
    let extent = phi.clone().or(psi.clone()).normal();
    let a1 = call("comp", [base2.clone(), extent.quote(), tube, a.clone()]);
    let b = call("glue", [gt.clone(), t, a1]);
    // Reverse the filling from a to a1. Under psi this is exactly snd w.
    let phi3 = lift_face(p, &phi2)?;
    let psi3 = lift_face(p, &psi2)?;
    let pp3 = lift(p, &pp2)?;
    let q3 = lift(p, &q2)?;
    let a3 = lift(p, &a2)?;
    let point = call("neg", [call("meet", [call("neg", [dim(1)]), dim(0)])]);
    let tube = system(&[
        (phi3, papp(pp3, point.clone())),
        (psi3, papp(q3, point)),
        (Face::End(1, true), a3),
    ]);
    let extent = phi2.or(psi2).or(Face::End(0, true)).normal();
    let family = lift(p, &base2)?;
    let path = call("plam", [call("comp", [family, extent.quote(), tube, a2])]);
    Ok(call("pair", [b, path]))
}
pub fn unglue_function() -> Sexp {
    call("lam", [call("unglue", [v(0)])])
}

// The contraction is built for any chosen Glue expression, not postulated.
pub fn glue_fiber_contraction(p: &mut RestrictedProducer, gt: &Sexp, a: &Sexp) -> Result<Sexp> {
    let Sexp::List(xs) = gt else {
        return Err("expected Glue".into());
    };
    let base = &xs[1];
    let f = unglue_function();
    let (fiber, _) = p.fiber_type(gt, base, &f, a)?;
    let center = glue_fiber_extension(p, gt, &Face::False, &atom("zero"), a)?;
    // Abstract both fiber elements to keep the center out of the tubes.
    let fiber1 = p.f.path.transform(&fiber, &Op::Shift(0))?.0;
    let fiber2 = p.f.path.transform(&fiber1, &Op::Shift(0))?.0;
    let family = lift(p, &fiber2)?;
    let prop_ty = call(
        "pi",
        [
            fiber.clone(),
            call(
                "pi",
                [
                    fiber1,
                    crate::cubical::engine::path_frontend::path(family, v(1), v(0)),
                ],
            ),
        ],
    );
    let gt1 = p.f.path.transform(gt, &Op::Shift(0))?.0;
    let gt2 = p.f.path.transform(&gt1, &Op::Shift(0))?.0;
    let gt_j = lift(p, &gt2)?;
    let a1 = p.f.path.transform(a, &Op::Shift(0))?.0;
    let a2 = p.f.path.transform(&a1, &Op::Shift(0))?.0;
    let a_j = lift(p, &a2)?;
    let partial = system(&[(Face::End(0, false), v(1)), (Face::End(0, true), v(0))]);
    let extent = Face::End(0, false).or(Face::End(0, true));
    let extension = glue_fiber_extension(p, &gt_j, &extent, &partial, &a_j)?;
    let prop = call("lam", [call("lam", [call("plam", [extension])])]);
    let contraction = call("app", [call("ann", [prop, prop_ty]), center.clone()]);
    Ok(call("pair", [center, contraction]))
}
pub fn unglue_equivalence(p: &mut RestrictedProducer, gt: &Sexp) -> Result<Sexp> {
    let gt_a = p.f.path.transform(gt, &Op::Shift(0))?.0;
    let witness = glue_fiber_contraction(p, &gt_a, &v(0))?;
    Ok(call("pair", [unglue_function(), call("lam", [witness])]))
}
pub fn glue_fiber_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    // a:B, e:Equiv A B, B:U, A:U; one free face direction.
    let (et, _) = p.equiv_type(&v(1), &v(0))?;
    let ge = cons(et.clone(), cons(u(0), cons(u(0), atom("nil"))));
    let g = cons(v(1), ge);
    let gt = call("glue-type", [v(2), Face::End(0, false).quote(), v(3), v(1)]);
    let f = unglue_function();
    p.check(1, &g, &Face::True, &f, &call("pi", [gt.clone(), v(3)]))?;
    let (fiber, _) = p.fiber_type(&gt, &v(2), &f, &v(0))?;
    let center = glue_fiber_extension(&mut p, &gt, &Face::False, &atom("zero"), &v(0))?;
    let id = p.check(1, &g, &Face::True, &center, &fiber)?;
    p.f.path.p.result("unglue-fiber-center", id);
    let witness = glue_fiber_contraction(&mut p, &gt, &v(0))?;
    let (contr, _) = p.contr_type(&fiber)?;
    let id = p.check(1, &g, &Face::True, &witness, &contr)?;
    p.f.path.p.result("unglue-fiber-contraction", id);
    let gt = call("glue-type", [v(1), Face::End(0, false).quote(), v(2), v(0)]);
    let equiv = unglue_equivalence(&mut p, &gt)?;
    let (eqv, _) = p.equiv_type(&gt, &v(1))?;
    let ty = call("pi", [u(0), call("pi", [u(0), call("pi", [et, eqv])])]);
    let term = (0..3).fold(equiv, |t, _| call("lam", [t]));
    let id = p.export_has(1, &atom("nil"), &term, &ty)?;
    p.f.path.p.result("closed-face-glue-unglue-equiv", id);
    Ok(p)
}
