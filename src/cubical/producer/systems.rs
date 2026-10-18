//! Untrusted construction of restricted evidence and coherent systems.
//! Branch terms may use native restricted typing and local type conversion;
//! every overlap and cover is certified, and partial goals retain their face.
use super::{Face, Interval, Op, Producer, Result, Term, call, context, number};
use crate::cubical::ast::system;

impl Producer {
    pub(super) fn transform_face(&mut self, f: &Face, op: &Op) -> Result<(Face, usize)> {
        let mut refs = Vec::new();
        let (out, suffix) = match f {
            Face::False => (Face::False, "ff"),
            Face::True => (Face::True, "ft"),
            Face::End(n, one) => {
                let replacement = if let Op::DSubst(_, r) = op {
                    Some(r)
                } else {
                    None
                };
                let (r, id) = self.itransform(
                    &Interval::Var(*n),
                    op.cutoff(),
                    replacement,
                    matches!(op, Op::DShift(_)),
                )?;
                refs.push(id);
                let n = if let Op::DShift(_) = op {
                    let Interval::Var(n) = r else {
                        unreachable!("shifting a dimension")
                    };
                    Face::End(n, *one)
                } else {
                    let (a, b, boundary) = self.boundary(&r)?;
                    refs.push(boundary);
                    if *one { b } else { a }
                };
                (n, if *one { "1" } else { "0" })
            }
            Face::And(a, b) | Face::Or(a, b) => {
                let (a, x) = self.transform_face(a, op)?;
                let (b, y) = self.transform_face(b, op)?;
                refs.extend([x, y]);
                if matches!(f, Face::And(..)) {
                    (Face::And(Box::new(a), Box::new(b)), "and")
                } else {
                    (Face::Or(Box::new(a), Box::new(b)), "or")
                }
            }
        };
        let pred = if matches!(op, Op::DShift(_)) {
            "fshift"
        } else {
            "fsubst"
        };
        let mut args = vec![f.quote(), number(op.cutoff())];
        if let Op::DSubst(_, r) = op {
            args.push(r.quote());
        }
        args.push(out.quote());
        let id = self.fact(&format!("{pred}.{suffix}"), refs, pred, args)?;
        Ok((out, id))
    }

    pub(super) fn transform_system(
        &mut self,
        sides: &[(Face, Term)],
        op: &Op,
    ) -> Result<(Vec<(Face, Term)>, usize)> {
        let pred = match op {
            Op::Shift(_) => "sshift",
            Op::Subst(..) => "ssubst",
            Op::DShift(_) => "sdshift",
            Op::DSubst(..) => "sdsubst",
        };
        let (out, refs, suffix) = match sides.split_first() {
            None => (Vec::new(), vec![], "nil"),
            Some(((face, t), rest)) => {
                let mut refs = Vec::new();
                let face = if matches!(op, Op::DShift(_) | Op::DSubst(..)) {
                    let (f, id) = self.transform_face(face, op)?;
                    refs.push(id);
                    f
                } else {
                    face.clone()
                };
                let (t, id) = self.transform(t, op)?;
                refs.push(id);
                let (rest, id) = self.transform_system(rest, op)?;
                refs.push(id);
                let mut out = vec![(face, t)];
                out.extend(rest);
                (out, refs, "side")
            }
        };
        let mut args = vec![system(sides), number(op.cutoff())];
        match op {
            Op::Subst(_, r) => args.push(r.quote()),
            Op::DSubst(_, r) => args.push(r.quote()),
            _ => {}
        }
        args.push(system(&out));
        let id = self.fact(&format!("{pred}.{suffix}"), refs, pred, args)?;
        Ok((out, id))
    }

    pub(super) fn restricted_evidence(
        &mut self,
        rule: &str,
        refs: Vec<usize>,
        scope: (usize, &[Term]),
        phi: &Face,
        terms: (&Term, &Term),
        ty: &Term,
    ) -> Result<usize> {
        let (d, g) = scope;
        self.fact(
            rule,
            refs,
            "req",
            vec![
                number(d),
                context(g),
                phi.quote(),
                terms.0.quote(),
                terms.1.quote(),
                ty.quote(),
            ],
        )
    }

    pub(super) fn restricted_check(
        &mut self,
        d: usize,
        g: &[Term],
        phi: &Face,
        t: &Term,
        ty: &Term,
    ) -> Result<usize> {
        self.face(d, phi)?;
        self.restricted_universe(d, g, phi, ty)?;
        if let Term::System(annotation, sides) = t {
            if annotation.quote() != ty.quote() {
                return Err("system annotation must match the requested type".into());
            }
            return self.system_has(d, g, phi, sides, ty);
        }
        let (actual, typed) = self.restricted_infer(d, g, phi, t)?;
        if actual.quote() == ty.quote() {
            return Ok(typed);
        }
        self.converting(|p| {
            let (i, _) = p.restricted_universe(d, g, phi, &actual)?;
            let (j, wf) = p.restricted_universe(d, g, phi, ty)?;
            if i != j {
                return Err(
                    "restricted type conversion requires the same universe level; no cumulativity"
                        .into(),
                );
            }
            let eq = p.restricted_equal((d, g), phi, &actual, ty, &Term::Universe(i))?;
            p.rhas("rhas.conv", vec![typed, eq, wf], (d, g), phi, t, ty)
        })
    }

    pub(super) fn local_path(
        &mut self,
        scope: (usize, &[Term]),
        phi: &Face,
        p: &Term,
        r: &Interval,
        s: &Interval,
        ty: &Term,
    ) -> Result<usize> {
        let (d, g) = scope;
        let (mut pty, mut typed) = self.restricted_infer(d, g, phi, p)?;
        if !matches!(pty, Term::Path(..)) {
            (pty, typed) = self
                .converting(|producer| producer.restricted_expose((d, g), phi, p, &pty, typed))?;
        }
        let Term::Path(a, _, _) = pty else {
            return Err("expected a path".into());
        };
        let (ar, x) = self.transform(&a, &Op::DSubst(0, r.clone()))?;
        let (as_, y) = self.transform(&a, &Op::DSubst(0, s.clone()))?;
        if ar.quote() != as_.quote() || ar.quote() != ty.quote() {
            return Err("restricted path congruence requires syntactically identical family instances and requested type".into());
        }
        let local = self.local(d, phi, r, s)?;
        let (_, kind) = self.restricted_universe(d, g, phi, &ar)?;
        let left = Term::PathApp(Box::new(p.clone()), r.clone());
        let right = Term::PathApp(Box::new(p.clone()), s.clone());
        self.restricted_evidence(
            "req.pdim-r",
            vec![typed, local, x, y, kind],
            scope,
            phi,
            (&left, &right),
            ty,
        )
    }

    pub(super) fn restricted_equal(
        &mut self,
        scope: (usize, &[Term]),
        phi: &Face,
        a: &Term,
        b: &Term,
        ty: &Term,
    ) -> Result<usize> {
        if self.restricted_depth >= 64 {
            return Err("restricted equality search exceeded depth 64".into());
        }
        self.restricted_depth += 1;
        let result = self.restricted_equal_inner(scope, phi, a, b, ty);
        self.restricted_depth -= 1;
        result
    }

    fn restricted_equal_inner(
        &mut self,
        scope: (usize, &[Term]),
        phi: &Face,
        a: &Term,
        b: &Term,
        ty: &Term,
    ) -> Result<usize> {
        let (d, g) = scope;
        let left = self.restricted_check(d, g, phi, a, ty)?;
        let right = self.restricted_check(d, g, phi, b, ty)?;
        if a.quote() == b.quote() {
            return self.restricted_evidence("req.refl", vec![left], scope, phi, (a, b), ty);
        }
        if let Ok(global) = self.equal(d, g, a, b, ty) {
            let face = self.face(d, phi)?;
            return self.restricted_evidence(
                "req.global",
                vec![face, global],
                scope,
                phi,
                (a, b),
                ty,
            );
        }
        if let Ok(empty) = self.entails(d, phi, &Face::False) {
            return self.restricted_evidence(
                "req.false",
                vec![empty, left, right],
                scope,
                phi,
                (a, b),
                ty,
            );
        }
        if let Some((out, actual, step)) = self.restricted_reduce(scope, phi, a)? {
            let step =
                self.restricted_convert_equality(scope, phi, (a, &out), (&actual, ty), step)?;
            let tail = self.restricted_equal(scope, phi, &out, b, ty)?;
            return self.restricted_evidence("req.trans", vec![step, tail], scope, phi, (a, b), ty);
        }
        if let Some((out, actual, step)) = self.restricted_reduce(scope, phi, b)? {
            let step =
                self.restricted_convert_equality(scope, phi, (b, &out), (&actual, ty), step)?;
            let reverse =
                self.restricted_evidence("req.sym", vec![step], scope, phi, (&out, b), ty)?;
            let head = self.restricted_equal(scope, phi, a, &out, ty)?;
            return self.restricted_evidence(
                "req.trans",
                vec![head, reverse],
                scope,
                phi,
                (a, b),
                ty,
            );
        }
        if let Term::System(_, sides) = a {
            let agrees = self.agrees(scope, phi, sides, b, ty)?;
            return self.restricted_evidence(
                "req.system-eq",
                vec![left, right, agrees],
                scope,
                phi,
                (a, b),
                ty,
            );
        }
        if matches!(b, Term::System(..)) {
            let reverse = self.restricted_equal(scope, phi, b, a, ty)?;
            return self.restricted_evidence("req.sym", vec![reverse], scope, phi, (a, b), ty);
        }
        if let (Term::PathApp(p, r), Term::PathApp(q, s)) = (a, b)
            && p.quote() == q.quote()
            && let Ok(local) = self.local_path(scope, phi, p, r, s, ty)
        {
            return Ok(local);
        }
        if let Term::PathApp(p, r) = a {
            let (mut pty, typed) = self.restricted_infer(d, g, phi, p)?;
            if !matches!(pty, Term::Path(..)) {
                pty = self
                    .converting(|producer| producer.restricted_expose((d, g), phi, p, &pty, typed))?
                    .0;
            }
            if let Term::Path(_, zero, one) = pty {
                for (endpoint, value) in [(Interval::Zero, *zero), (Interval::One, *one)] {
                    if *r == endpoint || a.quote() == value.quote() {
                        continue;
                    }
                    let attempt = |producer: &mut Self| -> Result<usize> {
                        let local = producer.local_path(scope, phi, p, r, &endpoint, ty)?;
                        let middle = Term::PathApp(p.clone(), endpoint);
                        let restricted =
                            producer.restricted_equal(scope, phi, &middle, &value, ty)?;
                        let head = producer.restricted_evidence(
                            "req.trans",
                            vec![local, restricted],
                            scope,
                            phi,
                            (a, &value),
                            ty,
                        )?;
                        let tail = producer.restricted_equal(scope, phi, &value, b, ty)?;
                        producer.restricted_evidence(
                            "req.trans",
                            vec![head, tail],
                            scope,
                            phi,
                            (a, b),
                            ty,
                        )
                    };
                    if let Ok(id) = attempt(self) {
                        return Ok(id);
                    }
                }
            }
        } else if matches!(b, Term::PathApp(..)) {
            let reverse = self.restricted_equal(scope, phi, b, a, ty)?;
            return self.restricted_evidence("req.sym", vec![reverse], scope, phi, (a, b), ty);
        }
        if let Face::Or(l, r) = phi {
            let cover = self.entails(d, phi, phi)?;
            let x = self.restricted_equal(scope, l, a, b, ty)?;
            let y = self.restricted_equal(scope, r, a, b, ty)?;
            return self.restricted_evidence(
                "req.cases",
                vec![cover, x, y],
                scope,
                phi,
                (a, b),
                ty,
            );
        }
        Err("restricted equality is not established by the supported evidence".into())
    }

    fn agrees(
        &mut self,
        scope: (usize, &[Term]),
        base: &Face,
        sides: &[(Face, Term)],
        target: &Term,
        ty: &Term,
    ) -> Result<usize> {
        let (rule, refs) = match sides.split_first() {
            None => ("agrees.nil", vec![]),
            Some(((phi, t), rest)) => {
                let overlap = Face::And(Box::new(base.clone()), Box::new(phi.clone()));
                let equal = self.restricted_equal(scope, &overlap, t, target, ty)?;
                let tail = self.agrees(scope, base, rest, target, ty)?;
                ("agrees.side", vec![equal, tail])
            }
        };
        self.fact(
            rule,
            refs,
            "agrees",
            vec![
                number(scope.0),
                context(scope.1),
                base.quote(),
                system(sides),
                target.quote(),
                ty.quote(),
            ],
        )
    }

    fn overlaps(
        &mut self,
        scope: (usize, &[Term]),
        base: &Face,
        phi: &Face,
        t: &Term,
        rest: &[(Face, Term)],
        ty: &Term,
    ) -> Result<usize> {
        let (rule, refs) = match rest.split_first() {
            None => ("overlaps.nil", vec![]),
            Some(((psi, u), tail)) => {
                let face = Face::And(
                    Box::new(Face::And(Box::new(base.clone()), Box::new(phi.clone()))),
                    Box::new(psi.clone()),
                );
                let equal = self.restricted_equal(scope, &face, t, u, ty)?;
                let rest = self.overlaps(scope, base, phi, t, tail, ty)?;
                ("overlaps.side", vec![equal, rest])
            }
        };
        self.fact(
            rule,
            refs,
            "overlaps",
            vec![
                number(scope.0),
                context(scope.1),
                base.quote(),
                phi.quote(),
                t.quote(),
                system(rest),
                ty.quote(),
            ],
        )
    }

    fn coherent(
        &mut self,
        scope: (usize, &[Term]),
        base: &Face,
        sides: &[(Face, Term)],
        ty: &Term,
    ) -> Result<(Face, usize)> {
        let (d, g) = scope;
        let (dom, rule, refs) = match sides.split_first() {
            None => {
                let restricted = self.restricted_ctx(d, g, base)?;
                (Face::False, "coherent.nil", vec![restricted])
            }
            Some(((phi, t), rest)) => {
                let face = self.face(d, phi)?;
                let overlap = Face::And(Box::new(base.clone()), Box::new(phi.clone()));
                let typed = self.restricted_check(d, g, &overlap, t, ty)?;
                let (dom, tail) = self.coherent(scope, base, rest, ty)?;
                let overlap = self.overlaps(scope, base, phi, t, rest, ty)?;
                (
                    Face::Or(Box::new(phi.clone()), Box::new(dom)),
                    "coherent.side",
                    vec![face, typed, tail, overlap],
                )
            }
        };
        let id = self.fact(
            rule,
            refs,
            "coherent",
            vec![
                number(d),
                context(g),
                base.quote(),
                system(sides),
                ty.quote(),
                dom.quote(),
            ],
        )?;
        Ok((dom, id))
    }

    pub(super) fn system_has(
        &mut self,
        d: usize,
        g: &[Term],
        base: &Face,
        sides: &[(Face, Term)],
        ty: &Term,
    ) -> Result<usize> {
        let (level, _) = self.restricted_universe(d, g, base, ty)?;
        let kind = self.restricted_check(d, g, base, ty, &Term::Universe(level))?;
        let (domain, coherent) = self.coherent((d, g), base, sides, ty)?;
        let cover = self.entails(d, base, &domain)?;
        self.fact(
            "rhas.system",
            vec![kind, coherent, cover],
            "rhas",
            vec![
                number(d),
                context(g),
                base.quote(),
                call("system", [system(sides)]),
                ty.quote(),
            ],
        )
    }

    pub(super) fn branch(&mut self, sides: &[(Face, Term)], i: usize) -> Result<usize> {
        let (rule, refs) = if i == 0 {
            ("branch.here", vec![])
        } else {
            ("branch.there", vec![self.branch(&sides[1..], i - 1)?])
        };
        self.fact(
            rule,
            refs,
            "branch",
            vec![system(sides), sides[i].0.quote(), sides[i].1.quote()],
        )
    }

    pub(super) fn reduce_system(
        &mut self,
        d: usize,
        g: &[Term],
        sides: &[(Face, Term)],
        ty: &Term,
    ) -> Result<Option<(Term, usize)>> {
        let typed = self.system_has(d, g, &Face::True, sides, ty)?;
        let term = Term::System(Box::new(ty.clone()), sides.to_vec());
        for (i, (phi, value)) in sides.iter().enumerate() {
            if let Ok(cover) = self.entails(d, &Face::True, phi) {
                let branch = self.branch(sides, i)?;
                let value_typed = self.restricted_check(d, g, &Face::True, value, ty)?;
                let restricted = self.restricted_evidence(
                    "req.system-branch",
                    vec![typed, branch, cover, value_typed],
                    (d, g),
                    &Face::True,
                    (&term, value),
                    ty,
                )?;
                let id =
                    self.equality_step("req.export", vec![restricted], (d, g), &term, value, ty)?;
                return Ok(Some((value.clone(), id)));
            }
        }
        Ok(None)
    }
}
