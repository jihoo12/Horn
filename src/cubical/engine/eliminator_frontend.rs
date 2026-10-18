//! Untrusted weak-head reduction through systems and neutral eliminators.
//! Only existing branch, congruence, conversion, and computation rules are used.
use super::{RestrictedProducer, shape};
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::Op;
use crate::cubical::engine::term::{Result, Sexp, atom, call};

impl RestrictedProducer {
    fn eliminator_redex(t: &Sexp) -> Result<bool> {
        Ok(match shape(t)? {
            ("ann" | "system" | "papp" | "comp" | "glue" | "unglue" | "glue-type" | "bif", _) => true,
            ("app", [f, _]) => shape(f)?.0 == "lam" || Self::eliminator_redex(f)?,
            ("fst" | "snd", [t]) => shape(t)?.0 == "pair" || Self::eliminator_redex(t)?,
            _ => false,
        })
    }
    fn branch_proof(&mut self, s: &Sexp, index: usize) -> Result<usize> {
        let ("side", [phi, value, rest]) = shape(s)? else {
            return Err("invalid branch index".into());
        };
        if index == 0 {
            return Ok(self.f.path.p.emit(
                "branch.here",
                vec![],
                call("branch", [s.clone(), phi.clone(), value.clone()]),
            ));
        }
        let id = self.branch_proof(rest, index - 1)?;
        let Sexp::List(j) = self.f.path.p.judgment(id) else {
            unreachable!()
        };
        let (phi, value) = (j[2].clone(), j[3].clone());
        Ok(self.f.path.p.emit(
            "branch.there",
            vec![id],
            call("branch", [s.clone(), phi, value]),
        ))
    }
    /// One step on an eliminator's head. With `keep_reduct_types`, a head
    /// `ann (system …) T` whose annotation was just removed also takes its
    /// active branch, since annotating the system again would undo the step.
    fn reduce_head(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        h: &Sexp,
    ) -> Result<(Sexp, Sexp, usize)> {
        let (h2, ty, e) = self.reduce(d, g, phi, h)?;
        if self.reduct_types && shape(h)?.0 == "ann" && shape(&h2)?.0 == "system" {
            let (h3, _, e2) = self.reduce_at(d, g, phi, &h2, &ty)?;
            if h3 != h2 {
                let e = self.eq(d, g, phi, h, &h3, &ty, "req.trans", vec![e, e2]);
                return Ok((h3, ty, e));
            }
        }
        Ok((h2, ty, e))
    }
    /// With `keep_reduct_types`, a reduct that needs an annotation (a
    /// system or an introduction form) stays annotated with the type it was
    /// reduced at, so that every later typing of a term built around it, and
    /// of every type mentioning it, can still infer it. Computation through
    /// such annotations is handled in `reduce_typed`.
    #[allow(clippy::too_many_arguments)] // Equation, reduct, and its type.
    pub(super) fn keep_type(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        reduct: Sexp,
        ty: &Sexp,
        eq: usize,
    ) -> Result<(Sexp, usize)> {
        if !self.reduct_types || !matches!(shape(&reduct)?.0, "system" | "lam" | "pair" | "plam") {
            return Ok((reduct, eq));
        }
        let annotated = call("ann", [reduct.clone(), ty.clone()]);
        let ai = self.check(d, g, phi, &annotated, ty)?;
        let ri = self.check(d, g, phi, &reduct, ty)?;
        let ann = self.eq(d, g, phi, &annotated, &reduct, ty, "req.ann", vec![ai, ri]);
        let back = self.eq(d, g, phi, &reduct, &annotated, ty, "req.sym", vec![ann]);
        let eq = self.eq(d, g, phi, t, &annotated, ty, "req.trans", vec![eq, back]);
        Ok((annotated, eq))
    }
    #[allow(clippy::too_many_arguments)] // An explicitly typed eliminator judgment.
    pub(super) fn reduce_eliminator(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        ty: &Sexp,
        ti: usize,
    ) -> Result<Option<(Sexp, Sexp, usize)>> {
        match shape(t)? {
            ("system", [s]) => {
                let mut rest = s;
                let mut index = 0;
                while let ("side", [face, value, tail]) = shape(rest)? {
                    if let Ok(cover) = self.f.entails(d, phi, &Face::parse(face)?) {
                        let branch = self.branch_proof(s, index)?;
                        let vi = self.check(d, g, phi, value, ty)?;
                        let eq = self.eq(
                            d,
                            g,
                            phi,
                            t,
                            value,
                            ty,
                            "req.system-branch",
                            vec![ti, branch, cover, vi],
                        );
                        let (value, eq) = self.keep_type(d, g, phi, t, value.clone(), ty, eq)?;
                        return Ok(Some((value, ty.clone(), eq)));
                    }
                    index += 1;
                    rest = tail;
                }
            }
            ("app", [f, arg]) if shape(f)?.0 != "lam" && Self::eliminator_redex(f)? => {
                let (f2, ft, ef) = self.reduce_head(d, g, phi, f)?;
                if f2 == *f {
                    return Ok(None);
                }
                let ("pi", [dom, cod]) = shape(&ft)? else {
                    return Err("eliminator application expects Pi".into());
                };
                let (f2, ef) = self.keep_type(d, g, phi, f, f2, &ft, ef)?;
                let out = call("app", [f2, arg.clone()]);
                let arg_i = self.check(d, g, phi, arg, dom)?;
                let ea = self.eq(d, g, phi, arg, arg, dom, "req.refl", vec![arg_i]);
                let (bt, si) = self.f.path.transform(cod, &Op::Subst(0, arg.clone()))?;
                let li = self.check(d, g, phi, t, &bt)?;
                let ri = self.check(d, g, phi, &out, &bt)?;
                let eq = self.eq(
                    d,
                    g,
                    phi,
                    t,
                    &out,
                    &bt,
                    "req.app-cong",
                    vec![ef, ea, si, li, ri],
                );
                let eq = self.retype_eq(d, g, phi, t, &out, &bt, ty, eq)?;
                return Ok(Some((out, ty.clone(), eq)));
            }
            ("papp", [line, r]) if shape(line)?.0 != "plam" && Self::eliminator_redex(line)? => {
                let (line2, line_ty, eline) = self.reduce(d, g, phi, line)?;
                if line2 == *line {
                    return Ok(None);
                }
                let ("path", [family, _, _]) = shape(&line_ty)? else {
                    return Err("path application reduction expects Path".into());
                };
                let out = call("papp", [line2, r.clone()]);
                let er = self.local_interval(d, phi, r, r)?;
                let (at, si) = self.f.path.transform(family, &Op::DSubst(0, r.clone()))?;
                let li = self.check(d, g, phi, t, &at)?;
                let ri = self.check(d, g, phi, &out, &at)?;
                let eq = self.eq(
                    d,
                    g,
                    phi,
                    t,
                    &out,
                    &at,
                    "req.papp-cong",
                    vec![eline, er, si, li, ri],
                );
                let eq = self.retype_eq(d, g, phi, t, &out, &at, ty, eq)?;
                return Ok(Some((out, ty.clone(), eq)));
            }
            ("unglue", [arg]) if Self::eliminator_redex(arg)? => {
                let (arg2, arg_ty, earg) = self.reduce(d, g, phi, arg)?;
                if arg2 == *arg {
                    return Ok(None);
                }
                let ("glue-type", [base, _, _, _]) = shape(&arg_ty)? else {
                    return Err("unglue reduction expects Glue".into());
                };
                let out = call("unglue", [arg2]);
                let li = self.check(d, g, phi, t, base)?;
                let ri = self.check(d, g, phi, &out, base)?;
                let eq = self.eq(
                    d,
                    g,
                    phi,
                    t,
                    &out,
                    base,
                    "req.unglue-cong",
                    vec![earg, li, ri],
                );
                let eq = self.retype_eq(d, g, phi, t, &out, base, ty, eq)?;
                return Ok(Some((out, ty.clone(), eq)));
            }
            (head @ ("fst" | "snd"), [arg])
                if shape(arg)?.0 != "pair" && Self::eliminator_redex(arg)? =>
            {
                let (arg2, arg_ty, earg) = self.reduce_head(d, g, phi, arg)?;
                if arg2 == *arg {
                    return Ok(None);
                }
                let ("sigma", [dom, cod]) = shape(&arg_ty)? else {
                    return Err("eliminator projection expects Sigma".into());
                };
                let (arg2, earg) = self.keep_type(d, g, phi, arg, arg2, &arg_ty, earg)?;
                let out = call(head, [arg2]);
                let mut refs = vec![earg];
                let result_ty = if head == "fst" {
                    dom.clone()
                } else {
                    let (bt, si) = self
                        .f
                        .path
                        .transform(cod, &Op::Subst(0, call("fst", [arg.clone()])))?;
                    refs.push(si);
                    bt
                };
                refs.push(self.check(d, g, phi, t, &result_ty)?);
                refs.push(self.check(d, g, phi, &out, &result_ty)?);
                let eq = self.eq(
                    d,
                    g,
                    phi,
                    t,
                    &out,
                    &result_ty,
                    if head == "fst" {
                        "req.fst-cong"
                    } else {
                        "req.snd-cong"
                    },
                    refs,
                );
                let eq = self.retype_eq(d, g, phi, t, &out, &result_ty, ty, eq)?;
                return Ok(Some((out, ty.clone(), eq)));
            }
            ("bif", [p, tt, f, b]) => {
                if let (head @ ("btrue" | "bfalse"), []) = shape(b)? {
                    let out = if head == "btrue" { tt } else { f };
                    let oi = self.check(d, g, phi, out, ty)?;
                    let rule = if head == "btrue" {
                        "req.bif-true"
                    } else {
                        "req.bif-false"
                    };
                    let eq = self.eq(d, g, phi, t, out, ty, rule, vec![ti, oi]);
                    return Ok(Some((out.clone(), ty.clone(), eq)));
                }
                let bool = atom("bool");
                let (b2, bty, eb) = self.reduce(d, g, phi, b)?;
                if b2 == *b {
                    return Ok(None);
                }
                let eb = self.retype_eq(d, g, phi, b, &b2, &bty, &bool, eb)?;
                let out = call("bif", [p.clone(), tt.clone(), f.clone(), b2]);
                let oi = self.check(d, g, phi, &out, ty)?;
                let gb = crate::cubical::engine::path_frontend::cons(bool.clone(), g.clone());
                let (up, pi) = self.infer(d, &gb, phi, p)?;
                let ep = self.eq(d, &gb, phi, p, p, &up, "req.refl", vec![pi]);
                let mut refs = vec![ti, oi, ep];
                for (branch, value) in [("btrue", tt), ("bfalse", f)] {
                    let (pv, si) = self.f.path.transform(p, &Op::Subst(0, atom(branch)))?;
                    let vi = self.check(d, g, phi, value, &pv)?;
                    let ev = self.eq(d, g, phi, value, value, &pv, "req.refl", vec![vi]);
                    refs.extend([si, ev]);
                }
                refs.push(eb);
                let eq = self.eq(d, g, phi, t, &out, ty, "req.bif-cong", refs);
                return Ok(Some((out, ty.clone(), eq)));
            }
            _ => (),
        }
        Ok(None)
    }
}
