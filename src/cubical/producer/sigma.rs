//! Untrusted dependent-pair evidence using the unchanged Sigma fragment.
use super::{Face, Op, Producer, Result, Term, extend};

impl Producer {
    fn sigma_subject(
        &mut self,
        scope: (usize, &[Term]),
        phi: &Face,
        p: &Term,
    ) -> Result<(Term, Term, usize)> {
        let (mut ty, mut typed) = self.restricted_infer(scope.0, scope.1, phi, p)?;
        if !matches!(ty, Term::Sigma(..)) {
            (ty, typed) =
                self.converting(|producer| producer.restricted_expose(scope, phi, p, &ty, typed))?;
        }
        let Term::Sigma(a, b) = ty else {
            return Err("projection requires a Sigma pair".into());
        };
        Ok((*a, *b, typed))
    }

    pub(super) fn sigma_infer(
        &mut self,
        scope: (usize, &[Term]),
        phi: &Face,
        t: &Term,
    ) -> Result<(Term, usize)> {
        use Term::*;
        let (d, g) = scope;
        let (ty, refs, rule) = match t {
            Sigma(a, b) => {
                let (i, x) = self.restricted_universe(d, g, phi, a)?;
                let (j, y) = self.restricted_universe(d, &extend(g, a), phi, b)?;
                (
                    Universe(i.max(j)),
                    vec![x, y, self.max(i, j)?],
                    "rhas.sigma",
                )
            }
            Pair(ty, first, second) => {
                let Sigma(a, b) = ty.as_ref() else {
                    return Err("pair annotation must be a Sigma type".into());
                };
                let (_, x) = self.restricted_universe(d, g, phi, a)?;
                let (j, y) = self.restricted_universe(d, &extend(g, a), phi, b)?;
                let left = self.restricted_check(d, g, phi, first, a)?;
                let (bt, sub) = self.transform(b, &Op::Subst(0, *first.clone()))?;
                let kind = self.restricted_check(d, g, phi, &bt, &Universe(j))?;
                let right = self.restricted_check(d, g, phi, second, &bt)?;
                (*ty.clone(), vec![x, y, left, sub, kind, right], "rhas.pair")
            }
            Fst(p) => {
                let (a, _, pair) = self.sigma_subject(scope, phi, p)?;
                let (_, kind) = self.restricted_universe(d, g, phi, &a)?;
                (a, vec![pair, kind], "rhas.fst")
            }
            Snd(p) => {
                let (_, b, pair) = self.sigma_subject(scope, phi, p)?;
                let (bt, sub) = self.transform(&b, &Op::Subst(0, Fst(p.clone())))?;
                let (_, kind) = self.restricted_universe(d, g, phi, &bt)?;
                (bt, vec![pair, sub, kind], "rhas.snd")
            }
            _ => return Err("expected Sigma syntax".into()),
        };
        let id = self.rhas(rule, refs, scope, phi, t, &ty)?;
        Ok((ty, id))
    }

    pub(super) fn sigma_reduce(
        &mut self,
        scope: (usize, &[Term]),
        phi: &Face,
        t: &Term,
    ) -> Result<Option<(Term, Term, usize)>> {
        use Term::*;
        let (Fst(p) | Snd(p)) = t else {
            return Ok(None);
        };
        let Pair(_, first, second) = p.as_ref() else {
            return Ok(None);
        };
        let (a, b, typed) = self.sigma_subject(scope, phi, p)?;
        let (out, ty, refs, rule) = if matches!(t, Fst(..)) {
            let left = self.restricted_check(scope.0, scope.1, phi, first, &a)?;
            (*first.clone(), a, vec![typed, left], "req.fst-beta")
        } else {
            let (bt, sub) = self.transform(&b, &Op::Subst(0, Fst(p.clone())))?;
            let right = self.restricted_check(scope.0, scope.1, phi, second, &bt)?;
            (*second.clone(), bt, vec![typed, sub, right], "req.snd-beta")
        };
        let id = self.restricted_evidence(rule, refs, scope, phi, (t, &out), &ty)?;
        Ok(Some((out, ty, id)))
    }

    pub(super) fn sigma_eta(
        &mut self,
        scope: (usize, &[Term]),
        phi: &Face,
        a: &Term,
        b: &Term,
        ty: &Term,
    ) -> Result<Option<usize>> {
        use Term::*;
        if let Pair(_, first, second) = a
            && let (Fst(p), Snd(q)) = (first.as_ref(), second.as_ref())
            && p.quote() == b.quote()
            && q.quote() == b.quote()
        {
            let (domain, body, typed) = self.sigma_subject(scope, phi, b)?;
            let actual = Sigma(Box::new(domain), Box::new(body));
            let pair = self.restricted_check(scope.0, scope.1, phi, a, &actual)?;
            let id = self.restricted_evidence(
                "req.pair-eta",
                vec![typed, pair],
                scope,
                phi,
                (a, b),
                &actual,
            )?;
            return self
                .restricted_convert_equality(scope, phi, (a, b), (&actual, ty), id)
                .map(Some);
        }
        if matches!(b, Pair(..))
            && !matches!(a, Pair(..))
            && let Some(reverse) = self.sigma_eta(scope, phi, b, a, ty)?
        {
            return self
                .restricted_evidence("req.sym", vec![reverse], scope, phi, (a, b), ty)
                .map(Some);
        }
        Ok(None)
    }
}
