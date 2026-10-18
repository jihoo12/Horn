//! Evidence for the unchanged Glue fragment. Partial types/equivalences are
//! checked on the attaching face; base values are checked on the ambient face.
use super::{Definition, Face, Producer, Result, Term};

impl Producer {
    fn glue_type(
        &mut self,
        scope: (usize, &[Term]),
        psi: &Face,
        gty: &Term,
    ) -> Result<(usize, usize)> {
        let Term::GlueType(a, phi, t, e) = gty else {
            return Err("glue annotation must be a literal Glue type".into());
        };
        let (d, g) = scope;
        let (l, base) = self.restricted_universe(d, g, psi, a)?;
        let face = self.face(d, phi)?;
        let overlap = Face::And(Box::new(psi.clone()), Box::new(phi.clone()));
        let partial = self.restricted_check(d, g, &overlap, t, &Term::Universe(l))?;
        let (et, expansion) = self.expand_definition(&Definition::Equiv(*t.clone(), *a.clone()))?;
        let kind = self.restricted_check(d, g, &overlap, &et, &Term::Universe(l))?;
        let equiv = self.restricted_check(d, g, &overlap, e, &et)?;
        let typed = self.rhas(
            "rhas.glue-type",
            vec![base, face, partial, expansion, kind, equiv],
            scope,
            psi,
            gty,
            &Term::Universe(l),
        )?;
        Ok((l, typed))
    }

    fn glue_subject(
        &mut self,
        scope: (usize, &[Term]),
        psi: &Face,
        u: &Term,
    ) -> Result<(Term, usize)> {
        let (mut ty, mut typed) = self.restricted_infer(scope.0, scope.1, psi, u)?;
        if !matches!(ty, Term::GlueType(..)) {
            (ty, typed) = self.converting(|p| p.restricted_expose(scope, psi, u, &ty, typed))?;
        }
        if !matches!(ty, Term::GlueType(..)) {
            return Err("unglue requires a Glue value".into());
        }
        Ok((ty, typed))
    }

    pub(super) fn glue_infer(
        &mut self,
        scope: (usize, &[Term]),
        psi: &Face,
        term: &Term,
    ) -> Result<(Term, usize)> {
        use Term::*;
        let (d, g) = scope;
        let (ty, refs, rule) = match term {
            GlueType(..) => {
                let (l, typed) = self.glue_type(scope, psi, term)?;
                return Ok((Universe(l), typed));
            }
            Glue(gty, u, v) => {
                let (_, typed) = self.glue_type(scope, psi, gty)?;
                let GlueType(a, phi, t, e) = gty.as_ref() else {
                    unreachable!()
                };
                let overlap = Face::And(Box::new(psi.clone()), Box::new(phi.clone()));
                let partial = self.restricted_check(d, g, &overlap, u, t)?;
                let base = self.restricted_check(d, g, psi, v, a)?;
                let mapped = App(Box::new(Fst(e.clone())), u.clone());
                let map = self.restricted_check(d, g, &overlap, &mapped, a)?;
                let compatible = self.restricted_equal(scope, &overlap, &mapped, v, a)?;
                (
                    *gty.clone(),
                    vec![typed, partial, base, map, compatible],
                    "rhas.glue",
                )
            }
            Unglue(u) => {
                let (gty, typed) = self.glue_subject(scope, psi, u)?;
                let GlueType(a, _, _, _) = gty else {
                    unreachable!()
                };
                let (_, kind) = self.restricted_universe(d, g, psi, &a)?;
                (*a, vec![typed, kind], "rhas.unglue")
            }
            _ => return Err("expected Glue syntax".into()),
        };
        let typed = self.rhas(rule, refs, scope, psi, term, &ty)?;
        Ok((ty, typed))
    }

    pub(super) fn glue_reduce(
        &mut self,
        scope: (usize, &[Term]),
        psi: &Face,
        term: &Term,
    ) -> Result<Option<(Term, Term, usize)>> {
        use Term::*;
        let (d, g) = scope;
        let (out, ty, refs, rule) = match term {
            GlueType(_, phi, t, _) => {
                let (l, typed) = self.glue_type(scope, psi, term)?;
                let Ok(cover) = self.entails(d, psi, phi) else {
                    return Ok(None);
                };
                let partial = self.restricted_check(d, g, psi, t, &Universe(l))?;
                (
                    *t.clone(),
                    Universe(l),
                    vec![typed, cover, partial],
                    "req.glue-type",
                )
            }
            Glue(gty, u, _) => {
                let (_, typed) = self.glue_infer(scope, psi, term)?;
                let GlueType(_, phi, t, _) = gty.as_ref() else {
                    unreachable!()
                };
                let Ok(cover) = self.entails(d, psi, phi) else {
                    return Ok(None);
                };
                let partial = self.restricted_check(d, g, psi, u, t)?;
                let converted = self.restricted_check(d, g, psi, term, t)?;
                (
                    *u.clone(),
                    *t.clone(),
                    vec![typed, cover, partial, converted],
                    "req.glue-face",
                )
            }
            Unglue(u) => {
                let (gty, typed) = self.glue_subject(scope, psi, u)?;
                let GlueType(a, phi, _, e) = gty else {
                    unreachable!()
                };
                if let Glue(_, _, v) = u.as_ref() {
                    let base = self.restricted_check(d, g, psi, v, &a)?;
                    (*v.clone(), *a, vec![typed, base], "req.unglue-beta")
                } else {
                    let Ok(cover) = self.entails(d, psi, &phi) else {
                        return Ok(None);
                    };
                    let mapped = App(Box::new(Fst(e)), u.clone());
                    let map = self.restricted_check(d, g, psi, &mapped, &a)?;
                    (mapped, *a, vec![typed, cover, map], "req.unglue-face")
                }
            }
            _ => return Ok(None),
        };
        let id = self.restricted_evidence(rule, refs, scope, psi, (term, &out), &ty)?;
        Ok(Some((out, ty, id)))
    }

    pub(super) fn glue_eta(
        &mut self,
        scope: (usize, &[Term]),
        psi: &Face,
        a: &Term,
        b: &Term,
        ty: &Term,
    ) -> Result<Option<usize>> {
        use Term::*;
        if let Glue(gty, u, v) = a
            && let Unglue(q) = v.as_ref()
            && u.quote() == b.quote()
            && q.quote() == b.quote()
        {
            let (actual, typed) = self.glue_subject(scope, psi, b)?;
            if gty.quote() != actual.quote() {
                return Ok(None);
            }
            let glued = self.restricted_check(scope.0, scope.1, psi, a, &actual)?;
            let id = self.restricted_evidence(
                "req.glue-eta",
                vec![typed, glued],
                scope,
                psi,
                (a, b),
                &actual,
            )?;
            return self
                .restricted_convert_equality(scope, psi, (a, b), (&actual, ty), id)
                .map(Some);
        }
        if matches!(b, Glue(..))
            && !matches!(a, Glue(..))
            && let Some(reverse) = self.glue_eta(scope, psi, b, a, ty)?
        {
            return self
                .restricted_evidence("req.sym", vec![reverse], scope, psi, (a, b), ty)
                .map(Some);
        }
        Ok(None)
    }
}
