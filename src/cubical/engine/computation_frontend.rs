//! Optional type-directed composition producer. The kernel remains generic.
use super::{RestrictedProducer, shape};
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{Op, dim};
use crate::cubical::engine::term::{Result, Sexp, atom, call};

impl RestrictedProducer {
    pub fn filling(&mut self, a: &Sexp, phi: &Face, t: &Sexp, b: &Sexp) -> Result<(Sexp, usize)> {
        let (a1, p) = self.f.path.transform(a, &Op::DShift(1))?;
        let (a2, q) = self.f.path.transform(&a1, &Op::DShift(1))?;
        let point = call("meet", [dim(1), dim(0)]);
        let (a3, r) = self.f.path.transform(&a2, &Op::DSubst(0, point.clone()))?;
        let (t1, s) = self.f.path.transform(t, &Op::DShift(1))?;
        let (t2, u) = self.f.path.transform(&t1, &Op::DShift(1))?;
        let (t3, v) = self.f.path.transform(&t2, &Op::DSubst(0, point))?;
        let (phi1, w) = self.f.path.ftransform(&phi.quote(), &Op::DShift(0))?;
        let (phi2, x) = self.f.path.ftransform(&phi1, &Op::DShift(0))?;
        let (b1, y) = self.f.path.transform(b, &Op::DShift(0))?;
        let (b2, z) = self.f.path.transform(&b1, &Op::DShift(0))?;
        let extent = call("for", [phi1, Face::End(0, false).quote()]);
        let tube = call(
            "system",
            [call(
                "side",
                [
                    phi2,
                    t3,
                    call("side", [Face::End(1, false).quote(), b2, atom("snil")]),
                ],
            )],
        );
        let fill = call("comp", [a3, extent, tube, b1]);
        let id = self.f.path.p.emit(
            "def.fill",
            vec![p, q, r, s, u, v, w, x, y, z],
            call(
                "filldef",
                [a.clone(), phi.quote(), t.clone(), b.clone(), fill.clone()],
            ),
        );
        Ok((fill, id))
    }
    pub fn canonical_program(&mut self, level: &Sexp) -> Result<(Sexp, usize)> {
        let source = include_str!("../../../theories/cubical/canonical-map.horn");
        let forms = crate::cubical::engine::term::parse(source)?;
        let rule=forms.iter().find(|f|matches!(f,Sexp::List(xs) if xs.len()==4 && xs[0]==atom("rule") && xs[1]==atom("def.canonical-map"))).ok_or("missing canonical program definition")?;
        let Sexp::List(rule) = rule else {
            unreachable!()
        };
        let Sexp::List(conclusion) = &rule[3] else {
            return Err("bad canonical definition".into());
        };
        fn instance(t: &Sexp, level: &Sexp) -> Sexp {
            match t {
                Sexp::Atom(a) if &**a == "?l" => level.clone(),
                Sexp::List(xs) => Sexp::List(xs.iter().map(|x| instance(x, level)).collect()),
                _ => t.clone(),
            }
        }
        let program = instance(&conclusion[2], level);
        let id = self.f.path.p.emit(
            "def.canonical-map",
            vec![],
            call("canonical-map", [level.clone(), program.clone()]),
        );
        Ok((program, id))
    }
    pub fn reverse_dimension(&mut self, t: &Sexp) -> Result<(Sexp, usize)> {
        let (t1, p) = self.f.path.transform(t, &Op::DShift(1))?;
        let (out, q) = self
            .f
            .path
            .transform(&t1, &Op::DSubst(0, call("neg", [dim(0)])))?;
        let id = self.f.path.p.emit(
            "def.reverse0",
            vec![p, q],
            call("reverse0", [t.clone(), out.clone()]),
        );
        Ok((out, id))
    }
    #[allow(clippy::too_many_arguments)] // Typed local computation judgment.
    pub(super) fn reduce_composition(
        &mut self,
        d: usize,
        g: &Sexp,
        psi: &Face,
        t: &Sexp,
        ty: &Sexp,
        ti: usize,
    ) -> Result<Option<(Sexp, Sexp, usize)>> {
        if let ("app", [f, arg]) = shape(t)?
            && let ("comp", [family, phi, tube, base]) = shape(f)?
            && let ("pi", [a, b]) = shape(family)?
        {
            let (ar, ari) = self.reverse_dimension(a)?;
            let (backfill, fi) = self.filling(&ar, &Face::False, &atom("zero"), arg)?;
            let (v, vi) = self.reverse_dimension(&backfill)?;
            let (g2, gi) = self.f.path.dshiftctx(g, 0)?;
            let (psi2, phii) = self.f.path.ftransform(&psi.quote(), &Op::DShift(0))?;
            let v_typed = self.check(d + 1, &g2, &Face::parse(&psi2)?, &v, a)?;
            let (bv, bi) = self.f.path.transform(b, &Op::Subst(0, v.clone()))?;
            let (v0, v0i) = self.f.path.transform(&v, &Op::DSubst(0, atom("i0")))?;
            let out = call(
                "comp",
                [
                    bv,
                    phi.clone(),
                    call("app", [tube.clone(), v]),
                    call("app", [base.clone(), v0]),
                ],
            );
            let oi = self.check(d, g, psi, &out, ty)?;
            let eq = self.eq(
                d,
                g,
                psi,
                t,
                &out,
                ty,
                "req.comp-pi-app",
                vec![ti, ari, fi, vi, gi, phii, v_typed, bi, v0i, oi],
            );
            return Ok(Some((out, ty.clone(), eq)));
        }
        let ("comp", [family, phi, tube, base]) = shape(t)? else {
            return Ok(None);
        };
        let extent = Face::parse(phi)?;
        if let ("glue-type", [a, glue_face, partial, equiv]) = shape(family)? {
            return self.reduce_glue_composition(
                d,
                g,
                psi,
                t,
                ty,
                ti,
                [a, glue_face, partial, equiv],
                [phi, tube, base],
            );
        }
        // A family that is itself a redex (for example a system whose branch
        // holds) is reduced under the composition binder first, by comp-cong.
        let family_head = shape(family)?.0;
        if matches!(
            family_head,
            "system" | "ann" | "papp" | "app" | "fst" | "snd" | "bif" | "comp" | "unglue" | "natrec"
                | "s1rec"
        ) || crate::cubical::engine::data::by_elim(family_head).is_some()
        {
            let (g2, gi) = self.f.path.dshiftctx(g, 0)?;
            let (psi2, psii) = self.f.path.ftransform(&psi.quote(), &Op::DShift(0))?;
            let psi2 = Face::parse(&psi2)?;
            let (family2, family_ty, efamily) = self.reduce(d + 1, &g2, &psi2, family)?;
            if family2 != *family {
                let (ua, _) = self.infer(d + 1, &g2, &psi2, family)?;
                let efamily =
                    self.retype_eq(d + 1, &g2, &psi2, family, &family2, &family_ty, &ua, efamily)?;
                let (phi2, phii) = self.f.path.ftransform(phi, &Op::DShift(0))?;
                let tube_face = psi2.and(Face::parse(&phi2)?);
                let tube_i = self.check(d + 1, &g2, &tube_face, tube, family)?;
                let etube = self.eq(d + 1, &g2, &tube_face, tube, tube, family, "req.refl", vec![tube_i]);
                let (a0, a0i) = self.f.path.transform(family, &Op::DSubst(0, atom("i0")))?;
                let base_i = self.check(d, g, psi, base, &a0)?;
                let ebase = self.eq(d, g, psi, base, base, &a0, "req.refl", vec![base_i]);
                let out = call("comp", [family2, phi.clone(), tube.clone(), base.clone()]);
                let oi = self.check(d, g, psi, &out, ty)?;
                let eq = self.eq(
                    d,
                    g,
                    psi,
                    t,
                    &out,
                    ty,
                    "req.comp-cong",
                    vec![ti, oi, gi, psii, phii, efamily, etube, a0i, ebase],
                );
                return Ok(Some((out, ty.clone(), eq)));
            }
        }
        if let Some(out) = self.comp_declared(d, g, psi, t, family, base, ty)? {
            return Ok(Some(out));
        }
        match shape(family)? {
            ("u", [level]) => {
                let (endpoint, ei) = self.f.path.transform(tube, &Op::DSubst(0, atom("i1")))?;
                let (reverse, ri) = self.reverse_dimension(tube)?;
                let (program, ci) = self.canonical_program(level)?;
                let ("ann", [value, program_type]) = shape(&program)? else {
                    return Err("canonical program needs a checked annotation".into());
                };
                let partial = psi.clone().and(extent.clone()).normal();
                if self.f.entails(d, &partial, &Face::False).is_err() {
                    // Type the ordinary library program before normalizing with
                    // the additional equations it helps to define. This only
                    // changes proof search; all typing steps are still checked.
                    let compute = self.type_directed_composition;
                    self.type_directed_composition = false;
                    let checked = (|| -> Result<()> {
                        self.check(d, &atom("nil"), &Face::True, value, program_type)?;
                        self.weaken_closed_annotation(d, g, &partial, value, program_type)?;
                        self.infer(d, g, &partial, &program)?;
                        Ok(())
                    })();
                    self.type_directed_composition = compute;
                    checked?;
                }
                let line = call(
                    "ann",
                    [
                        call("plam", [reverse]),
                        call("path", [family.clone(), endpoint.clone(), base.clone()]),
                    ],
                );
                let e = [endpoint.clone(), base.clone(), line]
                    .into_iter()
                    .fold(program, |t, a| call("app", [t, a]));
                let out = call("glue-type", [base.clone(), phi.clone(), endpoint, e]);
                let source = self.check(d, g, psi, t, family)?;
                let oi = self.check(d, g, psi, &out, family)?;
                let eq = self.eq(
                    d,
                    g,
                    psi,
                    t,
                    &out,
                    family,
                    "req.comp-universe",
                    vec![source, ei, ri, ci, oi],
                );
                let eq = self.retype_eq(d, g, psi, t, &out, family, ty, eq)?;
                Ok(Some((out, ty.clone(), eq)))
            }
            ("bool", []) => {
                let bool = atom("bool");
                let source = self.check(d, g, psi, t, &bool)?;
                let eq = self.eq(d, g, psi, t, base, &bool, "req.comp-bool", vec![source]);
                let eq = self.retype_eq(d, g, psi, t, base, &bool, ty, eq)?;
                Ok(Some((base.clone(), ty.clone(), eq)))
            }
            ("nat", []) => {
                let canonical = call(
                    "comp",
                    [atom("nat"), phi.clone(), atom("zero"), atom("zero")],
                );
                let prefix = if *t == canonical {
                    None
                } else {
                    let Ok(eq) = self.congruence(d, g, psi, t, &canonical, &atom("nat")) else {
                        // nat is discrete: any composition returns its base.
                        let nat = atom("nat");
                        let source = self.check(d, g, psi, t, &nat)?;
                        let eq = self.eq(d, g, psi, t, base, &nat, "req.comp-nat", vec![source]);
                        let eq = self.retype_eq(d, g, psi, t, base, &nat, ty, eq)?;
                        return Ok(Some((base.clone(), ty.clone(), eq)));
                    };
                    Some(eq)
                };
                let ci = self.check(d, g, psi, &canonical, &atom("nat"))?;
                let step = self.eq(
                    d,
                    g,
                    psi,
                    &canonical,
                    &atom("zero"),
                    &atom("nat"),
                    "req.comp-nat-zero",
                    vec![ci],
                );
                let eq = if let Some(prefix) = prefix {
                    self.eq(
                        d,
                        g,
                        psi,
                        t,
                        &atom("zero"),
                        &atom("nat"),
                        "req.trans",
                        vec![prefix, step],
                    )
                } else {
                    step
                };
                let eq = self.retype_eq(d, g, psi, t, &atom("zero"), &atom("nat"), ty, eq)?;
                Ok(Some((atom("zero"), ty.clone(), eq)))
            }
            ("sigma", [a, b]) => {
                let first_tube = call("fst", [tube.clone()]);
                let first_base = call("fst", [base.clone()]);
                let (fill, fi) = self.filling(a, &extent, &first_tube, &first_base)?;
                let (g2, gi) = self.f.path.dshiftctx(g, 0)?;
                let (psi2, phii) = self.f.path.ftransform(&psi.quote(), &Op::DShift(0))?;
                let fill_i = self.check(d + 1, &g2, &Face::parse(&psi2)?, &fill, a)?;
                let (bf, si) = self.f.path.transform(b, &Op::Subst(0, fill))?;
                let first = call("comp", [a.clone(), phi.clone(), first_tube, first_base]);
                let second = call(
                    "comp",
                    [
                        bf,
                        phi.clone(),
                        call("snd", [tube.clone()]),
                        call("snd", [base.clone()]),
                    ],
                );
                let out = call("pair", [first, second]);
                let oi = self.check(d, g, psi, &out, ty)?;
                let eq = self.eq(
                    d,
                    g,
                    psi,
                    t,
                    &out,
                    ty,
                    "req.comp-sigma",
                    vec![ti, fi, gi, phii, fill_i, si, oi],
                );
                Ok(Some((out, ty.clone(), eq)))
            }
            ("path", [a, left, right]) => {
                // Swap the original family dimensions j,i into i,j.
                let (a0, ai) = self.f.path.transform(a, &Op::DShift(0))?;
                let (family, swap) = self.f.path.transform(&a0, &Op::DSubst(2, dim(0)))?;
                let (phi1, pi) = self.f.path.ftransform(phi, &Op::DShift(0))?;
                let (phi2, pj) = self.f.path.ftransform(&phi1, &Op::DShift(0))?;
                let (tube, ts) = self.f.path.transform(tube, &Op::DShift(1))?;
                let (left, ls) = self.f.path.transform(left, &Op::DShift(1))?;
                let (right, rs) = self.f.path.transform(right, &Op::DShift(1))?;
                let (base, bs) = self.f.path.transform(base, &Op::DShift(0))?;
                let extent = call(
                    "for",
                    [
                        phi1,
                        call(
                            "for",
                            [Face::End(0, false).quote(), Face::End(0, true).quote()],
                        ),
                    ],
                );
                let tube = call(
                    "system",
                    [call(
                        "side",
                        [
                            phi2,
                            call("papp", [tube, dim(1)]),
                            call(
                                "side",
                                [
                                    Face::End(1, false).quote(),
                                    left,
                                    call("side", [Face::End(1, true).quote(), right, atom("snil")]),
                                ],
                            ),
                        ],
                    )],
                );
                let out = call(
                    "plam",
                    [call(
                        "comp",
                        [family, extent, tube, call("papp", [base, dim(0)])],
                    )],
                );
                let oi = self.check(d, g, psi, &out, ty)?;
                let eq = self.eq(
                    d,
                    g,
                    psi,
                    t,
                    &out,
                    ty,
                    "req.comp-path",
                    vec![ti, ai, swap, pi, pj, ts, ls, rs, bs, oi],
                );
                Ok(Some((out, ty.clone(), eq)))
            }
            _ => Ok(None),
        }
    }

    /// One `req.comp-glue` step for a composition `t` in a Glue type:
    /// the computed term and the equation's proof.
    pub fn glue_composition(
        &mut self,
        d: usize,
        g: &Sexp,
        psi0: &Face,
        t: &Sexp,
    ) -> Result<(Sexp, usize)> {
        let (ty, ti) = self.infer(d, g, psi0, t)?;
        let ("comp", [family, phi, tube, base]) = shape(t)? else {
            return Err("expected a composition".into());
        };
        let ("glue-type", [a, glue_face, partial, equiv]) = shape(family)? else {
            return Err("expected a Glue family".into());
        };
        let reduced = self.reduce_glue_composition(
            d,
            g,
            psi0,
            t,
            &ty,
            ti,
            [a, glue_face, partial, equiv],
            [phi, tube, base],
        )?;
        let (out, _, eq) = reduced.expect("Glue composition always reduces");
        Ok((out, eq))
    }
    /// `req.comp-glue`: composition in a Glue type (CCHM 6.2), built in the
    /// order of the rule's premises; see theories/computation.horn.
    #[allow(clippy::too_many_arguments)] // Typed local computation judgment.
    fn reduce_glue_composition(
        &mut self,
        d: usize,
        g: &Sexp,
        psi0: &Face,
        t: &Sexp,
        ty: &Sexp,
        ti: usize,
        [a, glue_face, partial, equiv]: [&Sexp; 4],
        [psi, tube, base]: [&Sexp; 3],
    ) -> Result<Option<(Sexp, Sexp, usize)>> {
        let fst = |x: Sexp| call("fst", [x]);
        let snd = |x: Sexp| call("snd", [x]);
        let app = |f: Sexp, x: Sexp| call("app", [f, x]);
        let unglue = |x: Sexp| call("unglue", [x]);
        let mut refs = vec![ti];
        let go = |p: &mut Self, x: &Sexp, op: Op, refs: &mut Vec<usize>| -> Result<Sexp> {
            let (out, id) = if op_is_face(x) {
                p.f.path.ftransform(x, &op)?
            } else {
                p.f.path.transform(x, &op)?
            };
            refs.push(id);
            Ok(out)
        };
        let (delta, di) = self.f.forall(&Face::parse(glue_face)?, 0)?;
        refs.push(di);
        let delta = delta.quote();
        let i1 = || Op::DSubst(0, atom("i1"));
        let a1 = go(self, a, i1(), &mut refs)?;
        let phi1 = go(self, glue_face, i1(), &mut refs)?;
        let t1 = go(self, partial, i1(), &mut refs)?;
        let e1 = go(self, equiv, i1(), &mut refs)?;
        let e0 = go(self, equiv, Op::DSubst(0, atom("i0")), &mut refs)?;
        let bend = go(self, tube, i1(), &mut refs)?;
        let (v, vi) = self.filling(partial, &Face::parse(psi)?, tube, base)?;
        refs.push(vi);
        let (et, eti) = self.equiv_type(partial, a)?;
        refs.push(eti);
        let et1 = go(self, &et, i1(), &mut refs)?;
        let et0 = go(self, &et, Op::DSubst(0, atom("i0")), &mut refs)?;
        let etj = go(self, &et, Op::DShift(1), &mut refs)?;
        let et0j = go(self, &et0, Op::DShift(0), &mut refs)?;
        let ann = |x: Sexp, ty: Sexp| call("ann", [x, ty]);
        let family = call(
            "glue-type",
            [a.clone(), glue_face.clone(), partial.clone(), equiv.clone()],
        );
        let g0 = go(self, &family, Op::DSubst(0, atom("i0")), &mut refs)?;
        let glue1 = call(
            "glue-type",
            [a1.clone(), phi1.clone(), t1.clone(), e1.clone()],
        );
        let g1k = go(self, &glue1, Op::DShift(0), &mut refs)?;
        let aj = go(self, a, Op::DShift(1), &mut refs)?;
        let ej = go(self, equiv, Op::DShift(1), &mut refs)?;
        let bj = go(self, tube, Op::DShift(1), &mut refs)?;
        let vj = go(self, &v, Op::DShift(1), &mut refs)?;
        let psij = go(self, psi, Op::DShift(0), &mut refs)?;
        let psijj = go(self, &psij, Op::DShift(0), &mut refs)?;
        let e0j = go(self, &e0, Op::DShift(0), &mut refs)?;
        let b0j = go(self, base, Op::DShift(0), &mut refs)?;
        let pres_tube = crate::cubical::engine::restricted_frontend::system(&[
            (
                Face::parse(&psijj)?,
                app(fst(ann(ej.clone(), etj.clone())), bj),
            ),
            (Face::End(1, true), app(fst(ann(ej, etj)), vj)),
        ]);
        let pres_extent = call("for", [psij, Face::End(0, true).quote()]);
        let omega = call(
            "plam",
            [call(
                "comp",
                [aj, pres_extent, pres_tube, app(fst(ann(e0j, et0j)), b0j)],
            )],
        );
        let omegaj = go(self, &omega, Op::DShift(0), &mut refs)?;
        let a1p = call(
            "comp",
            [
                a.clone(),
                psi.clone(),
                unglue(ann(tube.clone(), family)),
                unglue(ann(base.clone(), g0)),
            ],
        );
        let a1j = go(self, &a1p, Op::DShift(0), &mut refs)?;
        let e1a = ann(e1.clone(), et1);
        let (fib, fi) = self.fiber_type(&t1, &a1, &fst(e1a.clone()), &a1p)?;
        refs.push(fi);
        let fibk = go(self, &fib, Op::DShift(0), &mut refs)?;
        let center = app(snd(e1a), a1p.clone());
        let pk = go(self, &center, Op::DShift(0), &mut refs)?;
        let t1p = call(
            "comp",
            [partial.clone(), psi.clone(), tube.clone(), base.clone()],
        );
        let reversed = call("plam", [call("papp", [omegaj, call("neg", [dim(0)])])]);
        let u = crate::cubical::engine::restricted_frontend::system(&[
            (Face::parse(&delta)?, call("pair", [t1p, reversed])),
            (
                Face::parse(psi)?,
                call("pair", [bend.clone(), call("plam", [a1j])]),
            ),
        ]);
        let uk = go(self, &u, Op::DShift(0), &mut refs)?;
        let a1k = go(self, &a1, Op::DShift(0), &mut refs)?;
        let phi1k = go(self, &phi1, Op::DShift(0), &mut refs)?;
        let psik = go(self, psi, Op::DShift(0), &mut refs)?;
        let bendk = go(self, &bend, Op::DShift(0), &mut refs)?;
        let ext = call(
            "comp",
            [
                fibk,
                call("for", [delta, psi.clone()]),
                call("papp", [app(snd(pk), uk), dim(0)]),
                fst(center),
            ],
        );
        let alphak = go(self, &snd(ext.clone()), Op::DShift(0), &mut refs)?;
        let a1_tube = crate::cubical::engine::restricted_frontend::system(&[
            (
                Face::parse(&phi1k)?,
                call("papp", [alphak, call("neg", [dim(0)])]),
            ),
            (Face::parse(&psik)?, unglue(ann(bendk, g1k))),
        ]);
        let corrected = call(
            "comp",
            [a1k, call("for", [phi1.clone(), psi.clone()]), a1_tube, a1p],
        );
        let out = call("glue", [glue1, fst(ext), corrected]);
        refs.push(self.check(d, g, psi0, &out, ty)?);
        let eq = self.eq(d, g, psi0, t, &out, ty, "req.comp-glue", refs);
        Ok(Some((out, ty.clone(), eq)))
    }
}

/// Faces are transformed with ftransform, terms with transform.
fn op_is_face(x: &Sexp) -> bool {
    matches!(
        shape(x),
        Ok(("ff" | "ft" | "at0" | "at1" | "fand" | "for", _))
    )
}
