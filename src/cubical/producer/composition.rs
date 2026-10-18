//! Generate the existing composition typing and active-face computation
//! obligations. No regularity or type-directed composition equations are added.
use super::{Face, Interval, Op, Producer, Result, Term};

impl Producer {
    pub(super) fn composition_has(
        &mut self,
        scope: (usize, &[Term]),
        psi: &Face,
        t: &Term,
    ) -> Result<(Term, usize)> {
        let Term::Comp(a, phi, tube, base) = t else {
            return Err("expected composition".into());
        };
        let (d, g) = scope;
        let ctx = self.restricted_ctx(d, g, psi)?;
        let (g2, shifted) = self.dshiftctx(g)?;
        let (psi2, psi_shift) = self.transform_face(psi, &Op::DShift(0))?;
        let face = self.face(d, phi)?;
        let (phi2, phi_shift) = self.transform_face(phi, &Op::DShift(0))?;
        let (l, family) = self.restricted_universe(d + 1, &g2, &psi2, a)?;
        let tube_face = Face::And(Box::new(psi2), Box::new(phi2));
        let tube_id = self.restricted_check(d + 1, &g2, &tube_face, tube, a)?;
        let (a0, sub0) = self.transform(a, &Op::DSubst(0, Interval::Zero))?;
        let (a1, sub1) = self.transform(a, &Op::DSubst(0, Interval::One))?;
        let (t0, sub_tube) = self.transform(tube, &Op::DSubst(0, Interval::Zero))?;
        let kind0 = self.restricted_check(d, g, psi, &a0, &Term::Universe(l))?;
        let kind1 = self.restricted_check(d, g, psi, &a1, &Term::Universe(l))?;
        let base_id = self.restricted_check(d, g, psi, base, &a0)?;
        let start_face = Face::And(Box::new(psi.clone()), Box::new(phi.clone()));
        let compatible = self.restricted_equal(scope, &start_face, &t0, base, &a0)?;
        let id = self.rhas(
            "rhas.comp",
            vec![
                ctx, shifted, psi_shift, face, phi_shift, family, tube_id, sub0, sub1, sub_tube,
                kind0, kind1, base_id, compatible,
            ],
            scope,
            psi,
            t,
            &a1,
        )?;
        Ok((a1, id))
    }
}
