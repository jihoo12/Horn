//! Engine support for the circle (`theories/cubical/circle.horn`): typing,
//! the boundary of loop, the recursor's computation, and congruence.
use super::{RestrictedProducer, level, shape};
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{Op, path};
use crate::cubical::engine::term::{Result, Sexp, atom, call};

impl RestrictedProducer {
    pub(super) fn infer_circle(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
    ) -> Result<Option<(Sexp, String, Vec<usize>)>> {
        let s1 = atom("s1");
        Ok(Some(match shape(t)? {
            ("s1", []) => (call("u", [atom("z")]), "rhas.s1".into(), vec![self.ctx(d, g, phi)?]),
            ("base", []) => (s1, "rhas.base".into(), vec![self.ctx(d, g, phi)?]),
            ("loop", [r]) => {
                let ctx = self.ctx(d, g, phi)?;
                let ri = self.f.path.interval(d, r)?;
                (s1, "rhas.loop".into(), vec![ctx, ri])
            }
            ("s1rec", [a, b, lp, x]) => {
                let (ua, ai) = self.infer(d, g, phi, a)?;
                level(&ua)?;
                let bi = self.check(d, g, phi, b, a)?;
                let (a1, si) = self.f.path.transform(a, &Op::DShift(0))?;
                let li = self.check(d, g, phi, lp, &path(a1, b.clone(), b.clone()))?;
                let xi = self.check(d, g, phi, x, &s1)?;
                (a.clone(), "rhas.s1rec".into(), vec![ai, bi, si, li, xi])
            }
            _ => return Ok(None),
        }))
    }

    /// A loop at an endpoint is base; the recursor computes on base and on
    /// loop, and otherwise reduces its scrutinee.
    pub(super) fn reduce_circle(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        ty: &Sexp,
        ti: usize,
    ) -> Result<Option<(Sexp, Sexp, usize)>> {
        match shape(t)? {
            ("loop", [r]) => {
                for one in [false, true] {
                    if let Ok(local) = self.f.endpoint(d, phi, r, one) {
                        let rule = if one { "req.loop-1" } else { "req.loop-0" };
                        let s1 = atom("s1");
                        let li = self.check(d, g, phi, t, &s1)?;
                        let eq = self.eq(d, g, phi, t, &atom("base"), &s1, rule, vec![li, local]);
                        let eq = self.retype_eq(d, g, phi, t, &atom("base"), &s1, ty, eq)?;
                        return Ok(Some((atom("base"), ty.clone(), eq)));
                    }
                }
                Ok(None)
            }
            ("s1rec", [a, b, lp, x]) => {
                match shape(x)? {
                    ("base", []) => {
                        let bi = self.check(d, g, phi, b, a)?;
                        let ti = self.check(d, g, phi, t, a)?;
                        let eq = self.eq(d, g, phi, t, b, a, "req.s1rec-base", vec![ti, bi]);
                        let eq = self.retype_eq(d, g, phi, t, b, a, ty, eq)?;
                        return Ok(Some((b.clone(), ty.clone(), eq)));
                    }
                    ("loop", [r]) if self.f.endpoint(d, phi, r, false).is_err()
                        && self.f.endpoint(d, phi, r, true).is_err() =>
                    {
                        let out = call("papp", [lp.clone(), r.clone()]);
                        let oi = self.check(d, g, phi, &out, a)?;
                        let ti = self.check(d, g, phi, t, a)?;
                        let eq = self.eq(d, g, phi, t, &out, a, "req.s1rec-loop", vec![ti, oi]);
                        let eq = self.retype_eq(d, g, phi, t, &out, a, ty, eq)?;
                        return Ok(Some((out, ty.clone(), eq)));
                    }
                    _ => {}
                }
                let _ = ti;
                let s1 = atom("s1");
                let (x2, xty, ex) = self.reduce(d, g, phi, x)?;
                if x2 == *x {
                    return Ok(None);
                }
                let ex = self.retype_eq(d, g, phi, x, &x2, &xty, &s1, ex)?;
                let out = call("s1rec", [a.clone(), b.clone(), lp.clone(), x2]);
                let ti = self.check(d, g, phi, t, a)?;
                let oi = self.check(d, g, phi, &out, a)?;
                let eq = self.eq(d, g, phi, t, &out, a, "req.s1rec-cong", vec![ti, oi, ex]);
                let eq = self.retype_eq(d, g, phi, t, &out, a, ty, eq)?;
                Ok(Some((out, ty.clone(), eq)))
            }
            _ => Ok(None),
        }
    }

    pub(super) fn congruence_circle(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        a: &Sexp,
        b: &Sexp,
        ty: &Sexp,
    ) -> Result<Option<usize>> {
        match (shape(a)?, shape(b)?) {
            (("loop", [r]), ("loop", [s])) => {
                let s1 = atom("s1");
                let ai = self.check(d, g, phi, a, &s1)?;
                let local = self.local_interval(d, phi, r, s)?;
                let si = self.f.path.interval(d, s)?;
                let eq = self.eq(d, g, phi, a, b, &s1, "req.loop-cong", vec![ai, local, si]);
                Ok(Some(self.retype_eq(d, g, phi, a, b, &s1, ty, eq)?))
            }
            (("s1rec", [aa, ab, al, ax]), ("s1rec", [ba, bb, bl, bx]))
                if aa == ba && ab == bb && al == bl =>
            {
                let ai = self.check(d, g, phi, a, aa)?;
                let bi = self.check(d, g, phi, b, aa)?;
                let eq = self.equality(d, g, phi, ax, bx, &atom("s1"))?;
                let eq = self.eq(d, g, phi, a, b, aa, "req.s1rec-cong", vec![ai, bi, eq]);
                Ok(Some(self.retype_eq(d, g, phi, a, b, aa, ty, eq)?))
            }
            _ => Ok(None),
        }
    }
}
