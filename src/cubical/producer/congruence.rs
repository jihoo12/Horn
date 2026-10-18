//! Untrusted, bounded congruence evidence. Every dependent output is rechecked
//! at the rule's EXACT type. Available only in the explicitly selected profile.
use super::{Face, Op, Producer, Result, Term};

impl Producer {
    pub(super) fn congruence_subject(
        &mut self,
        scope: (usize, &[Term]),
        phi: &Face,
        t: &Term,
        head: fn(&Term) -> bool,
    ) -> Result<(Term, usize)> {
        let (mut ty, mut typed) = self.restricted_infer(scope.0, scope.1, phi, t)?;
        if !head(&ty) {
            (ty, typed) =
                self.converting(|p| p.restricted_expose_until(scope, phi, t, &ty, typed, head))?;
        }
        if !head(&ty) {
            return Err("congruence subject has the wrong type head".into());
        }
        Ok((ty, typed))
    }

    pub(super) fn reduce_congruence(
        &mut self,
        scope: (usize, &[Term]),
        phi: &Face,
        term: &Term,
    ) -> Result<Option<(Term, Term, usize)>> {
        use Term::*;
        let (d, g) = scope;
        let (out, ty, refs, rule) = match term {
            App(f, arg) => {
                let (fty, ftyped) =
                    self.congruence_subject(scope, phi, f, |t| matches!(t, Pi(..)))?;
                let Pi(a, b) = &fty else { unreachable!() };
                let (f2, arg2, fun_eq, arg_eq) = if let Some((f2, actual, eq)) =
                    self.restricted_reduce(scope, phi, f)?
                {
                    let eq = self.restricted_convert_equality(
                        scope,
                        phi,
                        (f, &f2),
                        (&actual, &fty),
                        eq,
                    )?;
                    let argtyped = self.restricted_check(d, g, phi, arg, a)?;
                    let arg_eq = self.restricted_evidence(
                        "req.refl",
                        vec![argtyped],
                        scope,
                        phi,
                        (arg, arg),
                        a,
                    )?;
                    (f2, *arg.clone(), eq, arg_eq)
                } else if let Some((arg2, actual, eq)) = self.restricted_reduce(scope, phi, arg)? {
                    let eq = self.restricted_convert_equality(
                        scope,
                        phi,
                        (arg, &arg2),
                        (&actual, a),
                        eq,
                    )?;
                    let fun_eq = self.restricted_evidence(
                        "req.refl",
                        vec![ftyped],
                        scope,
                        phi,
                        (f, f),
                        &fty,
                    )?;
                    (*f.clone(), arg2, fun_eq, eq)
                } else {
                    return Ok(None);
                };
                let out = App(Box::new(f2), Box::new(arg2));
                let (bt, sub) = self.transform(b, &Op::Subst(0, *arg.clone()))?;
                let left = self.restricted_check(d, g, phi, term, &bt)?;
                let right = self.restricted_check(d, g, phi, &out, &bt)?;
                (
                    out,
                    bt,
                    vec![fun_eq, arg_eq, sub, left, right],
                    "req.app-cong",
                )
            }
            Fst(p) | Snd(p) => {
                let (pty, _) =
                    self.congruence_subject(scope, phi, p, |t| matches!(t, Sigma(..)))?;
                let Some((p2, actual, eq)) = self.restricted_reduce(scope, phi, p)? else {
                    return Ok(None);
                };
                let eq =
                    self.restricted_convert_equality(scope, phi, (p, &p2), (&actual, &pty), eq)?;
                let Sigma(a, b) = &pty else { unreachable!() };
                let (out, ty, mut refs, rule) = if matches!(term, Fst(..)) {
                    (Fst(Box::new(p2)), *a.clone(), vec![eq], "req.fst-cong")
                } else {
                    let (bt, sub) = self.transform(b, &Op::Subst(0, Fst(p.clone())))?;
                    (Snd(Box::new(p2)), bt, vec![eq, sub], "req.snd-cong")
                };
                refs.push(self.restricted_check(d, g, phi, term, &ty)?);
                refs.push(self.restricted_check(d, g, phi, &out, &ty)?);
                (out, ty, refs, rule)
            }
            Unglue(p) => {
                let (pty, _) =
                    self.congruence_subject(scope, phi, p, |t| matches!(t, GlueType(..)))?;
                let Some((p2, actual, eq)) = self.restricted_reduce(scope, phi, p)? else {
                    return Ok(None);
                };
                let eq =
                    self.restricted_convert_equality(scope, phi, (p, &p2), (&actual, &pty), eq)?;
                let GlueType(a, _, _, _) = pty else {
                    unreachable!()
                };
                let out = Unglue(Box::new(p2));
                let left = self.restricted_check(d, g, phi, term, &a)?;
                let right = self.restricted_check(d, g, phi, &out, &a)?;
                (out, *a, vec![eq, left, right], "req.unglue-cong")
            }
            PathApp(p, r) => {
                let (pty, _) = self.congruence_subject(scope, phi, p, |t| matches!(t, Path(..)))?;
                let Some((p2, actual, eq)) = self.restricted_reduce(scope, phi, p)? else {
                    return Ok(None);
                };
                let eq =
                    self.restricted_convert_equality(scope, phi, (p, &p2), (&actual, &pty), eq)?;
                let Path(a, _, _) = pty else { unreachable!() };
                let local = self.local(d, phi, r, r)?;
                let (ar, sub) = self.transform(&a, &Op::DSubst(0, r.clone()))?;
                let out = PathApp(Box::new(p2), r.clone());
                let left = self.restricted_check(d, g, phi, term, &ar)?;
                let right = self.restricted_check(d, g, phi, &out, &ar)?;
                (out, ar, vec![eq, local, sub, left, right], "req.papp-cong")
            }
            _ => return Ok(None),
        };
        let id = self.restricted_evidence(rule, refs, scope, phi, (term, &out), &ty)?;
        Ok(Some((out, ty, id)))
    }
}
