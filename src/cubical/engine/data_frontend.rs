//! Engine support for user-declared data types (see `data.rs`): inference,
//! reduction, composition, congruence and value normalization, emitting the
//! generated rules with premises in the order the rule text states them.
use super::{RestrictedProducer, level, shape};
use crate::cubical::engine::data;
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{Op, cons, u, v};
use crate::cubical::engine::term::{Result, Sexp, atom, call};

impl RestrictedProducer {
    /// Typing of a declared type, constructor or eliminator.
    pub(super) fn infer_declared(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
    ) -> Result<Option<(Sexp, String, Vec<usize>)>> {
        let (head, args) = shape(t)?;
        if let Some(data) = data::by_type(head) {
            let ctx = self.ctx(d, g, phi)?;
            return Ok(Some((u(0), format!("rhas.{}", data.ty), vec![ctx])));
        }
        if let Some((data, i)) = data::by_ctor(head) {
            let c = &data.ctors[i];
            if args.len() != c.args.len() {
                return Err(format!("constructor {} expects {} arguments", c.name, c.args.len()));
            }
            let mut refs = vec![self.ctx(d, g, phi)?];
            for (a, ty) in args.iter().zip(&c.args) {
                refs.push(self.check(d, g, phi, a, ty)?);
            }
            return Ok(Some((atom(&data.ty), format!("rhas.{}", c.symbol), refs)));
        }
        let Some(data) = data::by_elim(head) else {
            return Ok(None);
        };
        let k = data.ctors.len();
        let [p, rest @ ..] = args else {
            return Err("eliminator without motive".into());
        };
        if rest.len() != k + 1 {
            return Err(format!("eliminator for {} expects {k} methods", data.name));
        }
        let (methods, x) = (&rest[..k], &rest[k]);
        let ty = atom(&data.ty);
        let (up, pi) = self.infer(d, &cons(ty.clone(), g.clone()), phi, p)?;
        let l = level(&up)?;
        let mut refs = vec![pi];
        for (i, c) in data.ctors.iter().enumerate() {
            let (ihs, depth, codomain_args) = data.method_plan(i);
            let mut ih_types = Vec::new();
            for &(shifts, var) in &ihs {
                let base = self.shift_chain(p, shifts, &mut refs)?;
                let (ih, si) = self.f.path.transform(&base, &Op::Subst(0, v(var)))?;
                refs.push(si);
                ih_types.push(ih);
            }
            let base = self.shift_chain(p, depth, &mut refs)?;
            let applied = data::ctor_term(c, codomain_args.iter().map(|&n| v(n)).collect());
            let (mut method_ty, si) = self.f.path.transform(&base, &Op::Subst(0, applied))?;
            refs.push(si);
            for ih in ih_types.into_iter().rev() {
                method_ty = call("pi", [ih, method_ty]);
            }
            for a in c.args.iter().rev() {
                method_ty = call("pi", [a.clone(), method_ty]);
            }
            refs.push(self.check(d, g, phi, &methods[i], &method_ty)?);
        }
        refs.push(self.check(d, g, phi, x, &ty)?);
        let (px, si) = self.f.path.transform(p, &Op::Subst(0, x.clone()))?;
        refs.push(si);
        refs.push(self.check(d, g, phi, &px, &u(l))?);
        Ok(Some((px, format!("rhas.{}", data.elim), refs)))
    }

    fn shift_chain(&mut self, p: &Sexp, n: usize, refs: &mut Vec<usize>) -> Result<Sexp> {
        let mut cur = p.clone();
        for _ in 0..n {
            let (next, id) = self.f.path.transform(&cur, &Op::Shift(1))?;
            refs.push(id);
            cur = next;
        }
        Ok(cur)
    }

    /// One computation or congruence step of a declared eliminator.
    pub(super) fn reduce_declared(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        ty: &Sexp,
        ti: usize,
    ) -> Result<Option<(Sexp, Sexp, usize)>> {
        let (head, args) = shape(t)?;
        let Some(data) = data::by_elim(head) else {
            return Ok(None);
        };
        let k = data.ctors.len();
        let (p, methods, x) = (&args[0], &args[1..=k], &args[k + 1]);
        let (xh, xargs) = shape(x)?;
        if let Some((_, i)) = data::by_ctor(xh) {
            let c = &data.ctors[i];
            let mut out = methods[i].clone();
            for a in xargs {
                out = call("app", [out, a.clone()]);
            }
            for &j in &c.recursive {
                let mut rec = vec![p.clone()];
                rec.extend(methods.iter().cloned());
                rec.push(xargs[j].clone());
                out = call("app", [out, call(head, rec)]);
            }
            let oi = self.check(d, g, phi, &out, ty)?;
            let rule = format!("req.{}.{}", data.elim, c.symbol);
            let eq = self.eq(d, g, phi, t, &out, ty, &rule, vec![ti, oi]);
            return Ok(Some((out, ty.clone(), eq)));
        }
        let dty = atom(&data.ty);
        let (x2, xty, ex) = self.reduce(d, g, phi, x)?;
        if x2 == *x {
            return Ok(None);
        }
        let ex = self.retype_eq(d, g, phi, x, &x2, &xty, &dty, ex)?;
        let mut items = args[..=k].to_vec();
        items.push(x2);
        let out = call(head, items);
        let oi = self.check(d, g, phi, &out, ty)?;
        let rule = format!("req.{}-cong", data.elim);
        let eq = self.eq(d, g, phi, t, &out, ty, &rule, vec![ti, oi, ex]);
        Ok(Some((out, ty.clone(), eq)))
    }

    /// Composition in a declared type returns its base.
    pub(super) fn comp_declared(
        &mut self,
        d: usize,
        g: &Sexp,
        psi: &Face,
        t: &Sexp,
        family: &Sexp,
        base: &Sexp,
        ty: &Sexp,
    ) -> Result<Option<(Sexp, Sexp, usize)>> {
        let Some(data) = data::by_type(family.atom().unwrap_or("")) else {
            return Ok(None);
        };
        let dty = atom(&data.ty);
        let source = self.check(d, g, psi, t, &dty)?;
        let rule = format!("req.comp-{}", data.ty);
        let eq = self.eq(d, g, psi, t, base, &dty, &rule, vec![source]);
        let eq = self.retype_eq(d, g, psi, t, base, &dty, ty, eq)?;
        Ok(Some((base.clone(), ty.clone(), eq)))
    }

    /// Congruence of two applications of the same constructor, or of two
    /// eliminations with the same motive and methods.
    pub(super) fn congruence_declared(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        a: &Sexp,
        b: &Sexp,
        ty: &Sexp,
    ) -> Result<Option<usize>> {
        let ((ah, ax), (bh, bx)) = (shape(a)?, shape(b)?);
        if ah != bh {
            return Ok(None);
        }
        if let Some((data, i)) = data::by_ctor(ah) {
            let c = &data.ctors[i];
            if ax.is_empty() {
                return Ok(None);
            }
            let mut refs = Vec::new();
            for ((x, y), arg_ty) in ax.iter().zip(bx).zip(&c.args) {
                refs.push(self.equality(d, g, phi, x, y, arg_ty)?);
            }
            let dty = atom(&data.ty);
            let eq = self.eq(d, g, phi, a, b, &dty, &format!("req.{}-cong", c.symbol), refs);
            return Ok(Some(self.retype_eq(d, g, phi, a, b, &dty, ty, eq)?));
        }
        if let Some(data) = data::by_elim(ah) {
            let k = data.ctors.len();
            if ax[..=k] != bx[..=k] {
                return Ok(None);
            }
            let ai = self.check(d, g, phi, a, ty)?;
            let bi = self.check(d, g, phi, b, ty)?;
            let eq = self.equality(d, g, phi, &ax[k + 1], &bx[k + 1], &atom(&data.ty))?;
            let rule = format!("req.{}-cong", data.elim);
            return Ok(Some(self.eq(d, g, phi, a, b, ty, &rule, vec![ai, bi, eq])));
        }
        Ok(None)
    }

    /// Normalize a constructor value's arguments, recursively.
    pub(super) fn value_declared(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        w: &Sexp,
        ty: &Sexp,
        fuel: usize,
    ) -> Result<Option<(Sexp, usize)>> {
        let Some(_) = data::by_type(ty.atom().unwrap_or("")) else {
            return Ok(None);
        };
        let (head, args) = shape(w)?;
        let Some((data, i)) = data::by_ctor(head) else {
            return Ok(None);
        };
        if args.is_empty() {
            return Ok(None);
        }
        let c = &data.ctors[i];
        let (mut out, mut refs, mut changed) = (Vec::new(), Vec::new(), false);
        for (a, arg_ty) in args.iter().zip(&c.args) {
            let (av, ea) = self.value(d, g, phi, a, arg_ty, fuel)?;
            changed |= av != *a;
            out.push(av);
            refs.push(ea);
        }
        if !changed {
            return Ok(None);
        }
        let out = call(head, out);
        let eq = self.eq(d, g, phi, w, &out, ty, &format!("req.{}-cong", c.symbol), refs);
        Ok(Some((out, eq)))
    }
}
