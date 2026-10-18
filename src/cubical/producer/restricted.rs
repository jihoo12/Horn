//! Native face-restricted typing. This is an untrusted proof searcher: every
//! local conversion and binder obligation uses the existing restricted rules.
use super::{Face, Interval, Op, Producer, Result, Term, call, context, extend, number};

impl Producer {
    pub(super) fn rhas(
        &mut self,
        rule: &str,
        refs: Vec<usize>,
        scope: (usize, &[Term]),
        phi: &Face,
        t: &Term,
        ty: &Term,
    ) -> Result<usize> {
        self.fact(
            rule,
            refs,
            "rhas",
            vec![
                number(scope.0),
                context(scope.1),
                phi.quote(),
                t.quote(),
                ty.quote(),
            ],
        )
    }

    pub(super) fn restricted_ctx(&mut self, d: usize, g: &[Term], phi: &Face) -> Result<usize> {
        let key = call("rctx", [number(d), context(g), phi.quote()]);
        if let Some(&id) = self.known.get(&key) {
            return Ok(id);
        }
        let (rule, refs) = match g.split_last() {
            None => ("rctx.nil", vec![self.face(d, phi)?]),
            Some((a, prefix)) => {
                let tail = self.restricted_ctx(d, prefix, phi)?;
                let (_, head) = self.restricted_universe(d, prefix, phi, a)?;
                ("rctx.cons", vec![tail, head])
            }
        };
        self.emit(rule, refs, key)
    }

    pub(super) fn restricted_universe(
        &mut self,
        d: usize,
        g: &[Term],
        phi: &Face,
        t: &Term,
    ) -> Result<(usize, usize)> {
        let (ty, typed) = self.restricted_infer(d, g, phi, t)?;
        if let Term::Universe(l) = ty {
            return Ok((l, typed));
        }
        self.converting(|p| {
            let (normal, typed) = p.restricted_expose((d, g), phi, t, &ty, typed)?;
            match normal {
                Term::Universe(l) => Ok((l, typed)),
                _ => Err(format!(
                    "expected a type under the face, got {} : {}",
                    t.quote(),
                    normal.quote()
                )),
            }
        })
    }

    pub(super) fn restricted_expose(
        &mut self,
        scope: (usize, &[Term]),
        phi: &Face,
        t: &Term,
        ty: &Term,
        typed: usize,
    ) -> Result<(Term, usize)> {
        let (d, g) = scope;
        let (level, _) = self.restricted_universe(d, g, phi, ty)?;
        let kind = Term::Universe(level);
        let mut normal = ty.clone();
        let mut id = typed;
        for reductions in 0..=32 {
            let Some((out, actual, equality)) = self.restricted_reduce(scope, phi, &normal)? else {
                return Ok((normal, id));
            };
            if reductions == 32 {
                return Err("restricted type exposure exceeded 32 root reductions".into());
            }
            let equality = self.restricted_convert_equality(
                scope,
                phi,
                (&normal, &out),
                (&actual, &kind),
                equality,
            )?;
            let wf = self.restricted_check(d, g, phi, &out, &kind)?;
            id = self.rhas("rhas.conv", vec![id, equality, wf], scope, phi, t, &out)?;
            normal = out;
        }
        unreachable!()
    }

    pub(super) fn restricted_infer(
        &mut self,
        d: usize,
        g: &[Term],
        phi: &Face,
        t: &Term,
    ) -> Result<(Term, usize)> {
        use Term::*;
        let key = (d, g.to_vec(), phi.clone(), t.clone());
        if let Some(out) = self.restricted_inferred.get(&key) {
            return Ok(out.clone());
        }
        self.face(d, phi)?;
        // Fast path retains compact proofs for already global terms. Failure
        // does not imply local failure: native rules below use the face.
        if let Ok((ty, global)) = self.infer(d, g, t) {
            let face = self.face(d, phi)?;
            let id = self.rhas("rhas.global", vec![face, global], (d, g), phi, t, &ty)?;
            self.restricted_inferred.insert(key, (ty.clone(), id));
            return Ok((ty, id));
        }
        let (ty, refs, rule) = match t {
            Universe(l) => (
                Universe(l + 1),
                vec![self.restricted_ctx(d, g, phi)?],
                "rhas.u",
            ),
            Nat => (
                Universe(0),
                vec![self.restricted_ctx(d, g, phi)?],
                "rhas.nat",
            ),
            Zero => (Nat, vec![self.restricted_ctx(d, g, phi)?], "rhas.zero"),
            Var(n) => {
                let ctx = self.restricted_ctx(d, g, phi)?;
                let (ty, lookup) = self.lookup(g, *n)?;
                (ty, vec![ctx, lookup], "rhas.v")
            }
            Pi(a, b) => {
                let (i, x) = self.restricted_universe(d, g, phi, a)?;
                let (j, y) = self.restricted_universe(d, &extend(g, a), phi, b)?;
                (Universe(i.max(j)), vec![x, y, self.max(i, j)?], "rhas.pi")
            }
            Lam(a, body) => {
                let (_, x) = self.restricted_universe(d, g, phi, a)?;
                let inner = extend(g, a);
                let (b, y) = self.restricted_infer(d, &inner, phi, body)?;
                let (_, z) = self.restricted_universe(d, &inner, phi, &b)?;
                (Pi(a.clone(), Box::new(b)), vec![x, y, z], "rhas.lam")
            }
            App(f, a) => {
                let (mut fty, mut x) = self.restricted_infer(d, g, phi, f)?;
                if !matches!(fty, Pi(..)) {
                    (fty, x) = self.converting(|p| p.restricted_expose((d, g), phi, f, &fty, x))?;
                }
                let Pi(domain, codomain) = fty else {
                    return Err("restricted application requires a function".into());
                };
                let y = self.restricted_check(d, g, phi, a, &domain)?;
                let (out, z) = self.transform(&codomain, &Op::Subst(0, *a.clone()))?;
                let (_, u) = self.restricted_universe(d, g, phi, &out)?;
                (out, vec![x, y, z, u], "rhas.app")
            }
            Path(a, b, _) | PathLam(a, b) => {
                let ctx = self.restricted_ctx(d, g, phi)?;
                let (inner, shifted) = self.dshiftctx(g)?;
                let (phi2, face_shift) = self.transform_face(phi, &Op::DShift(0))?;
                let (l, family) = self.restricted_universe(d + 1, &inner, &phi2, a)?;
                let (a0, x) = self.transform(a, &Op::DSubst(0, Interval::Zero))?;
                let (a1, y) = self.transform(a, &Op::DSubst(0, Interval::One))?;
                let u0 = self.restricted_check(d, g, phi, &a0, &Universe(l))?;
                let u1 = self.restricted_check(d, g, phi, &a1, &Universe(l))?;
                if let Path(_, _, c) = t {
                    let b = self.restricted_check(d, g, phi, b, &a0)?;
                    let c = self.restricted_check(d, g, phi, c, &a1)?;
                    (
                        Universe(l),
                        vec![ctx, shifted, face_shift, family, x, y, u0, u1, b, c],
                        "rhas.path",
                    )
                } else {
                    let body = self.restricted_check(d + 1, &inner, &phi2, b, a)?;
                    let (b0, z) = self.transform(b, &Op::DSubst(0, Interval::Zero))?;
                    let (b1, w) = self.transform(b, &Op::DSubst(0, Interval::One))?;
                    let v0 = self.restricted_check(d, g, phi, &b0, &a0)?;
                    let v1 = self.restricted_check(d, g, phi, &b1, &a1)?;
                    (
                        Path(a.clone(), Box::new(b0), Box::new(b1)),
                        vec![
                            ctx, shifted, face_shift, family, body, x, y, z, w, u0, u1, v0, v1,
                        ],
                        "rhas.plam",
                    )
                }
            }
            PathApp(p, r) => {
                let (mut pty, mut x) = self.restricted_infer(d, g, phi, p)?;
                if !matches!(pty, Path(..)) {
                    (pty, x) =
                        self.converting(|p2| p2.restricted_expose((d, g), phi, p, &pty, x))?;
                }
                let Path(a, _, _) = pty else {
                    return Err("restricted path application requires a path".into());
                };
                let y = self.interval(d, r)?;
                let (out, z) = self.transform(&a, &Op::DSubst(0, r.clone()))?;
                let (_, u) = self.restricted_universe(d, g, phi, &out)?;
                (out, vec![x, y, z, u], "rhas.papp")
            }
            Comp(..) => {
                let out = self.composition_has((d, g), phi, t)?;
                self.restricted_inferred.insert(key, out.clone());
                return Ok(out);
            }
            System(ty, sides) => {
                let id = self.system_has(d, g, phi, sides, ty)?;
                self.restricted_inferred.insert(key, (*ty.clone(), id));
                return Ok((*ty.clone(), id));
            }
        };
        let id = self.rhas(rule, refs, (d, g), phi, t, &ty)?;
        self.restricted_inferred.insert(key, (ty.clone(), id));
        Ok((ty, id))
    }

    pub(super) fn restricted_convert_equality(
        &mut self,
        scope: (usize, &[Term]),
        phi: &Face,
        terms: (&Term, &Term),
        types: (&Term, &Term),
        id: usize,
    ) -> Result<usize> {
        let (actual, expected) = types;
        if actual.quote() == expected.quote() {
            return Ok(id);
        }
        self.converting(|p| {
            let (i, _) = p.restricted_universe(scope.0, scope.1, phi, actual)?;
            let (j, wf) = p.restricted_universe(scope.0, scope.1, phi, expected)?;
            if i != j {
                return Err(
                    "restricted equality conversion requires the same universe level".into(),
                );
            }
            let eq = p.restricted_equal(scope, phi, actual, expected, &Term::Universe(i))?;
            p.restricted_evidence("req.conv", vec![id, eq, wf], scope, phi, terms, expected)
        })
    }

    /// One root step, with its actual equality type retained for req.conv.
    pub(super) fn restricted_reduce(
        &mut self,
        scope: (usize, &[Term]),
        phi: &Face,
        t: &Term,
    ) -> Result<Option<(Term, Term, usize)>> {
        use Term::*;
        let (d, g) = scope;
        let (out, ty, refs, rule) = match t {
            Comp(_, face, tube, _) => {
                let (ty, typed) = self.composition_has(scope, phi, t)?;
                let Ok(cover) = self.entails(d, phi, face) else {
                    return Ok(None);
                };
                let (out, sub) = self.transform(tube, &Op::DSubst(0, Interval::One))?;
                let output = self.restricted_check(d, g, phi, &out, &ty)?;
                (out, ty, vec![typed, cover, sub, output], "req.comp-face")
            }
            System(ty, sides) => {
                let typed = self.system_has(d, g, phi, sides, ty)?;
                for (i, (face, value)) in sides.iter().enumerate() {
                    if let Ok(cover) = self.entails(d, phi, face) {
                        let branch = self.branch(sides, i)?;
                        let output = self.restricted_check(d, g, phi, value, ty)?;
                        let id = self.restricted_evidence(
                            "req.system-branch",
                            vec![typed, branch, cover, output],
                            scope,
                            phi,
                            (t, value),
                            ty,
                        )?;
                        return Ok(Some((value.clone(), *ty.clone(), id)));
                    }
                }
                return Ok(None);
            }
            App(f, r) if matches!(f.as_ref(), Lam(..)) => {
                let (ty, typed) = self.restricted_infer(d, g, phi, t)?;
                let Lam(_, body) = f.as_ref() else {
                    unreachable!()
                };
                let (out, sub) = self.transform(body, &Op::Subst(0, *r.clone()))?;
                let output = self.restricted_check(d, g, phi, &out, &ty)?;
                (out, ty, vec![typed, sub, output], "req.beta-typed")
            }
            PathApp(p, r) => {
                let (mut pty, mut typed) = self.restricted_infer(d, g, phi, p)?;
                if !matches!(pty, Path(..)) {
                    (pty, typed) =
                        self.converting(|p2| p2.restricted_expose(scope, phi, p, &pty, typed))?;
                }
                let Path(a, b, c) = pty else {
                    return Err("expected a restricted path".into());
                };
                let (ty, subty) = self.transform(&a, &Op::DSubst(0, r.clone()))?;
                if let PathLam(_, body) = p.as_ref() {
                    let interval = self.interval(d, r)?;
                    let (out, sub) = self.transform(body, &Op::DSubst(0, r.clone()))?;
                    let output = self.restricted_check(d, g, phi, &out, &ty)?;
                    (
                        out,
                        ty,
                        vec![typed, interval, subty, sub, output],
                        "req.pbeta-r",
                    )
                } else if matches!(r, Interval::Zero | Interval::One) {
                    let (_, kind) = self.restricted_universe(d, g, phi, &ty)?;
                    let out = if *r == Interval::Zero { *b } else { *c };
                    let output = self.restricted_check(d, g, phi, &out, &ty)?;
                    (
                        out,
                        ty,
                        vec![typed, subty, kind, output],
                        if *r == Interval::Zero {
                            "req.p0-r"
                        } else {
                            "req.p1-r"
                        },
                    )
                } else {
                    for endpoint in [Interval::Zero, Interval::One] {
                        if self.local(d, phi, r, &endpoint).is_err() {
                            continue;
                        }
                        let middle = PathApp(p.clone(), endpoint.clone());
                        if let Ok(local) = self.local_path(scope, phi, p, r, &endpoint, &ty)
                            && let Some((out, actual, step)) =
                                self.restricted_reduce(scope, phi, &middle)?
                        {
                            let step = self.restricted_convert_equality(
                                scope,
                                phi,
                                (&middle, &out),
                                (&actual, &ty),
                                step,
                            )?;
                            let id = self.restricted_evidence(
                                "req.trans",
                                vec![local, step],
                                scope,
                                phi,
                                (t, &out),
                                &ty,
                            )?;
                            return Ok(Some((out, ty, id)));
                        }
                    }
                    return Ok(None);
                }
            }
            _ => return Ok(None),
        };
        let id = self.restricted_evidence(rule, refs, scope, phi, (t, &out), &ty)?;
        Ok(Some((out, ty, id)))
    }
}
