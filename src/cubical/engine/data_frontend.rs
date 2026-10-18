//! Engine support for user-declared data types (see `data.rs`). Typing runs
//! the same premise plans that generate the rule text; reduction,
//! composition, congruence and value normalization emit the generated
//! computation rules.
use super::{RestrictedProducer, shape};
use crate::cubical::engine::data::{self, Data, Plan, Prem, Tpl};
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{Op, cons, u};
use crate::cubical::engine::term::{Result, Sexp, atom, call};
use std::collections::HashMap;

fn inst(t: &Tpl, env: &HashMap<String, Sexp>) -> Result<Sexp> {
    Ok(match t {
        Tpl::Var(v) => env.get(v).cloned().ok_or_else(|| format!("unbound plan variable {v}"))?,
        Tpl::Ground(s) => s.clone(),
        Tpl::App(h, xs) => call(h, xs.iter().map(|x| inst(x, env)).collect::<Result<Vec<_>>>()?),
    })
}

impl RestrictedProducer {
    /// Emit the premises of `plan` in order, binding its variables in `env`.
    fn run_plan(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        plan: &Plan,
        env: &mut HashMap<String, Sexp>,
    ) -> Result<Vec<usize>> {
        let mut refs = Vec::new();
        for prem in &plan.prems {
            match prem {
                Prem::Ctx => refs.push(self.ctx(d, g, phi)?),
                Prem::Has { ext, term, ty } => {
                    let ctx = match ext {
                        Some(e) => cons(inst(e, env)?, g.clone()),
                        None => g.clone(),
                    };
                    let term = inst(term, env)?;
                    // A universe whose level is still open is inferred.
                    if let Tpl::App(h, xs) = ty
                        && h == "u"
                        && let [Tpl::Var(l)] = xs.as_slice()
                        && !env.contains_key(l)
                    {
                        let (found, id) = self.infer(d, &ctx, phi, &term)?;
                        let ("u", [level]) = shape(&found)? else {
                            return Err(format!("expected a type, found {term} : {found}"));
                        };
                        env.insert(l.clone(), level.clone());
                        refs.push(id);
                    } else {
                        let ty = inst(ty, env)?;
                        refs.push(self.check(d, &ctx, phi, &term, &ty)?);
                    }
                }
                Prem::Shift { from, cutoff, to } => {
                    let from = env[from].clone();
                    let (out, id) = self.f.path.transform(&from, &Op::Shift(*cutoff))?;
                    env.insert(to.clone(), out);
                    refs.push(id);
                }
                Prem::Subst { from, by, to } => {
                    let from = env[from].clone();
                    let by = inst(by, env)?;
                    let (out, id) = self.f.path.transform(&from, &Op::Subst(0, by))?;
                    env.insert(to.clone(), out);
                    refs.push(id);
                }
            }
        }
        Ok(refs)
    }

    /// Typing of a declared type, constructor or eliminator.
    pub(super) fn infer_declared(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
    ) -> Result<Option<(Sexp, String, Vec<usize>)>> {
        let (head, args) = shape(t)?;
        let mut env = HashMap::new();
        let bind_params = |env: &mut HashMap<String, Sexp>, data: &Data| {
            for (j, a) in args.iter().take(data.params).enumerate() {
                env.insert(format!("A{j}"), a.clone());
            }
        };
        let (plan, rule) = if let Some(data) = data::by_type(head) {
            if args.len() != data.params {
                return Err(format!("{} expects {} parameters", data.name, data.params));
            }
            bind_params(&mut env, &data);
            (data.formation_plan(), format!("rhas.{}", data.ty))
        } else if let Some((data, i)) = data::by_ctor(head) {
            let c = &data.ctors[i];
            if args.len() != data.params + c.args.len() {
                return Err(format!(
                    "constructor {} expects {} arguments",
                    c.name,
                    data.params + c.args.len()
                ));
            }
            bind_params(&mut env, &data);
            for (k, a) in args[data.params..].iter().enumerate() {
                env.insert(format!("a{k}"), a.clone());
            }
            (data.ctor_plan(i), format!("rhas.{}", c.symbol))
        } else if let Some(data) = data::by_elim(head) {
            let k = data.ctors.len();
            if args.len() != data.params + k + 2 {
                return Err(format!("eliminator for {} expects {k} methods", data.name));
            }
            bind_params(&mut env, &data);
            let rest = &args[data.params..];
            env.insert("p".into(), rest[0].clone());
            for i in 0..k {
                env.insert(format!("m{i}"), rest[1 + i].clone());
            }
            env.insert("x".into(), rest[k + 1].clone());
            (data.elim_plan(), format!("rhas.{}", data.elim))
        } else {
            return Ok(None);
        };
        let refs = self.run_plan(d, g, phi, &plan, &mut env)?;
        Ok(Some((inst(&plan.ty, &env)?, rule, refs)))
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
        let (np, k) = (data.params, data.ctors.len());
        let fixed = &args[..np + 1 + k];
        let methods = &args[np + 1..np + 1 + k];
        let x = &args[np + 1 + k];
        let (xh, xargs) = shape(x)?;
        if let Some((owner, i)) = data::by_ctor(xh)
            && owner.elim == data.elim
        {
            let c = &data.ctors[i];
            let fields = &xargs[np.min(xargs.len())..];
            let mut out = methods[i].clone();
            for a in fields {
                out = call("app", [out, a.clone()]);
            }
            for j in c.recursive() {
                let mut rec = fixed.to_vec();
                rec.push(fields[j].clone());
                out = call("app", [out, call(head, rec)]);
            }
            let oi = self.check(d, g, phi, &out, ty)?;
            let rule = format!("req.{}.{}", data.elim, c.symbol);
            let eq = self.eq(d, g, phi, t, &out, ty, &rule, vec![ti, oi]);
            return Ok(Some((out, ty.clone(), eq)));
        }
        let dty = data::apply(&data.ty, args[..np].to_vec());
        let (x2, xty, ex) = self.reduce(d, g, phi, x)?;
        if x2 == *x {
            return Ok(None);
        }
        let ex = self.retype_eq(d, g, phi, x, &x2, &xty, &dty, ex)?;
        let mut items = fixed.to_vec();
        items.push(x2);
        let out = call(head, items);
        let oi = self.check(d, g, phi, &out, ty)?;
        let rule = format!("req.{}-cong", data.elim);
        let eq = self.eq(d, g, phi, t, &out, ty, &rule, vec![ti, oi, ex]);
        Ok(Some((out, ty.clone(), eq)))
    }

    /// Composition in a declared type: a closed type returns its base; a
    /// parameterized one transports constructorwise along the empty face.
    #[allow(clippy::too_many_arguments)]
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
        let (fh, params) = shape(family)?;
        let Some(data) = data::by_type(fh) else {
            return Ok(None);
        };
        if data.params == 0 {
            let dty = atom(&data.ty);
            let source = self.check(d, g, psi, t, &dty)?;
            let rule = format!("req.comp-{}", data.ty);
            let eq = self.eq(d, g, psi, t, base, &dty, &rule, vec![source]);
            let eq = self.retype_eq(d, g, psi, t, base, &dty, ty, eq)?;
            return Ok(Some((base.clone(), ty.clone(), eq)));
        }
        let ("comp", [_, face, _, _]) = shape(t)? else {
            return Ok(None);
        };
        let (bh, bargs) = shape(base)?;
        let Some((owner, i)) = data::by_ctor(bh) else {
            return Ok(None);
        };
        if *face != atom("ff") || owner.ty != data.ty {
            return Ok(None);
        }
        let c = &data.ctors[i];
        let mut refs = vec![self.check(d, g, psi, t, ty)?];
        let mut parts = Vec::new();
        for a in params {
            let (end, id) = self.f.path.transform(a, &Op::DSubst(0, atom("i1")))?;
            refs.push(id);
            parts.push(end);
        }
        for (a, arg_ty) in bargs[data.params..].iter().zip(&c.args) {
            let line = data.field_type(arg_ty, params);
            parts.push(call("comp", [line, atom("ff"), atom("zero"), a.clone()]));
        }
        let out = data::apply(&c.symbol, parts);
        refs.push(self.check(d, g, psi, &out, ty)?);
        let rule = format!("req.comp-{}.{}", data.ty, c.symbol);
        let eq = self.eq(d, g, psi, t, &out, ty, &rule, refs);
        Ok(Some((out, ty.clone(), eq)))
    }

    /// Congruence of two applications of the same constructor at the same
    /// parameters, or of two eliminations differing only in the scrutinee.
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
        if let Some(data) = data::by_type(ah)
            && data.params > 0
        {
            let mut refs = Vec::new();
            for (x, y) in ax.iter().zip(bx) {
                refs.push(self.equality(d, g, phi, x, y, &u(0))?);
            }
            let eq = self.eq(d, g, phi, a, b, &u(0), &format!("req.{}-cong", data.ty), refs);
            return Ok(Some(self.retype_eq(d, g, phi, a, b, &u(0), ty, eq)?));
        }
        if let Some((data, i)) = data::by_ctor(ah) {
            let (np, c) = (data.params, &data.ctors[i]);
            if c.args.is_empty() && np == 0 {
                return Ok(None);
            }
            let mut refs = Vec::new();
            for (x, y) in ax[..np].iter().zip(&bx[..np]) {
                refs.push(self.equality(d, g, phi, x, y, &u(0))?);
            }
            for ((x, y), arg_ty) in ax[np..].iter().zip(&bx[np..]).zip(&c.args) {
                let field_ty = data.field_type(arg_ty, &ax[..np]);
                refs.push(self.equality(d, g, phi, x, y, &field_ty)?);
            }
            let dty = data::apply(&data.ty, ax[..np].to_vec());
            let eq = self.eq(d, g, phi, a, b, &dty, &format!("req.{}-cong", c.symbol), refs);
            return Ok(Some(self.retype_eq(d, g, phi, a, b, &dty, ty, eq)?));
        }
        if let Some(data) = data::by_elim(ah) {
            let fixed = data.params + 1 + data.ctors.len();
            if ax[..fixed] != bx[..fixed] {
                return Ok(None);
            }
            let ai = self.check(d, g, phi, a, ty)?;
            let bi = self.check(d, g, phi, b, ty)?;
            let dty = data::apply(&data.ty, ax[..data.params].to_vec());
            let eq = self.equality(d, g, phi, &ax[fixed], &bx[fixed], &dty)?;
            let rule = format!("req.{}-cong", data.elim);
            return Ok(Some(self.eq(d, g, phi, a, b, ty, &rule, vec![ai, bi, eq])));
        }
        Ok(None)
    }

    /// Normalize a constructor value's fields, recursively.
    pub(super) fn value_declared(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        w: &Sexp,
        ty: &Sexp,
        fuel: usize,
    ) -> Result<Option<(Sexp, usize)>> {
        let (head, args) = shape(w)?;
        // A parameterized type, as a value of a universe: normalize its
        // parameters.
        if let Some(data) = data::by_type(head)
            && data.params > 0
            && shape(ty)?.0 == "u"
        {
            let (mut out, mut refs, mut changed) = (Vec::new(), Vec::new(), false);
            for a in args {
                let (av, ea) = self.value(d, g, phi, a, &u(0), fuel)?;
                changed |= av != *a;
                out.push(av);
                refs.push(ea);
            }
            if !changed {
                return Ok(None);
            }
            let out = call(head, out);
            let eq = self.eq(d, g, phi, w, &out, &u(0), &format!("req.{}-cong", data.ty), refs);
            let eq = self.retype_eq(d, g, phi, w, &out, &u(0), ty, eq)?;
            return Ok(Some((out, eq)));
        }
        let Some(_) = data::by_type(shape(ty)?.0) else {
            return Ok(None);
        };
        let Some((data, i)) = data::by_ctor(head) else {
            return Ok(None);
        };
        let (np, c) = (data.params, &data.ctors[i]);
        if c.args.is_empty() && np == 0 {
            return Ok(None);
        }
        // Parameters are types; normalize them too, for readable values.
        let (mut out, mut refs, mut changed) = (Vec::new(), Vec::new(), false);
        for a in &args[..np] {
            let (av, ea) = self.whnf(d, g, phi, a, &u(0), fuel)?;
            changed |= av != *a;
            out.push(av);
            refs.push(ea);
        }
        for (a, arg_ty) in args[np..].iter().zip(&c.args) {
            let field_ty = data.field_type(arg_ty, &args[..np]);
            let (av, ea) = self.value(d, g, phi, a, &field_ty, fuel)?;
            changed |= av != *a;
            out.push(av);
            refs.push(ea);
        }
        if !changed {
            return Ok(None);
        }
        let out = call(head, out);
        let dty = data::apply(&data.ty, args[..np].to_vec());
        let eq = self.eq(d, g, phi, w, &out, &dty, &format!("req.{}-cong", c.symbol), refs);
        let eq = self.retype_eq(d, g, phi, w, &out, &dty, ty, eq)?;
        Ok(Some((out, eq)))
    }
}
