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
        Tpl::Var(v) => env
            .get(v)
            .cloned()
            .ok_or_else(|| format!("unbound plan variable {v}"))?,
        Tpl::Ground(s) => s.clone(),
        Tpl::App(h, xs) => call(
            h,
            xs.iter()
                .map(|x| inst(x, env))
                .collect::<Result<Vec<_>>>()?,
        ),
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
                    let from = inst(from, env)?;
                    let (out, id) = self.f.path.transform(&from, &Op::Shift(*cutoff))?;
                    env.insert(to.clone(), out);
                    refs.push(id);
                }
                Prem::DShift { from, to } => {
                    let from = env[from].clone();
                    let (out, id) = self.f.path.transform(&from, &Op::DShift(0))?;
                    env.insert(to.clone(), out);
                    refs.push(id);
                }
                Prem::Interval(i) => {
                    let r = env[i].clone();
                    refs.push(self.f.path.interval(d, &r)?);
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
            if args.len() != c.arity() {
                return Err(format!(
                    "constructor {} expects {} arguments",
                    c.name,
                    c.arity()
                ));
            }
            if c.boundary.is_some() {
                env.insert("i".into(), args[c.args.len()].clone());
            }
            // Parameters come from the types of fields at a parameter, or
            // of a recursive field.
            for (a, arg_ty) in args.iter().zip(&c.args) {
                if (0..data.params).all(|j| env.contains_key(&format!("A{j}"))) {
                    break;
                }
                match arg_ty {
                    data::ArgTy::Param(j) if !env.contains_key(&format!("A{j}")) => {
                        let (ty, _) = self.infer(d, g, phi, a)?;
                        env.insert(format!("A{j}"), ty);
                    }
                    data::ArgTy::Rec => {
                        let Ok((ty, _)) = self.infer(d, g, phi, a) else {
                            continue;
                        };
                        let Ok(ty) = self.declared_type(d, g, phi, &data, &ty) else {
                            continue;
                        };
                        for (j, p) in shape(&ty)?.1.iter().enumerate() {
                            env.insert(format!("A{j}"), p.clone());
                        }
                    }
                    _ => {}
                }
            }
            if (0..data.params).any(|j| !env.contains_key(&format!("A{j}"))) {
                return Err(format!("constructor {} needs an expected type", c.name));
            }
            for (k, a) in args.iter().take(c.args.len()).enumerate() {
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

    /// A declared type as its own head applied to its parameters: `ty`, or
    /// its weak-head normal form.
    fn declared_type(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        data: &Data,
        ty: &Sexp,
    ) -> Result<Sexp> {
        if data.params == 0 || shape(ty)?.0 == data.ty {
            return Ok(if data.params == 0 {
                atom(&data.ty)
            } else {
                ty.clone()
            });
        }
        let (universe, _) = self.infer(d, g, phi, ty)?;
        let target = self
            .whnf(d, g, phi, ty, &universe, super::super::FUEL_TYPES)?
            .0;
        if shape(&target)?.0 != data.ty {
            return Err(format!("{ty} is not {}", data.name));
        }
        Ok(target)
    }

    /// Check a constructor of a parameterized type against an expected type,
    /// whose weak-head normal form supplies the parameters.
    pub(super) fn check_declared(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        expected: &Sexp,
    ) -> Result<Option<usize>> {
        let (head, args) = shape(t)?;
        let Some((data, i)) = data::by_ctor(head) else {
            return Ok(None);
        };
        if data.params == 0 {
            return Ok(None);
        }
        let target = self
            .declared_type(d, g, phi, &data, expected)
            .map_err(|_| {
                format!(
                    "constructor {} checked against {expected}",
                    data.ctors[i].name
                )
            })?;
        let params = shape(&target)?.1;
        let c = &data.ctors[i];
        if args.len() != c.arity() {
            return Err(format!(
                "constructor {} expects {} arguments",
                c.name,
                c.arity()
            ));
        }
        let mut env = HashMap::new();
        if c.boundary.is_some() {
            env.insert("i".into(), args[c.args.len()].clone());
        }
        for (j, a) in params.iter().enumerate() {
            env.insert(format!("A{j}"), a.clone());
        }
        for (k, a) in args.iter().take(c.args.len()).enumerate() {
            env.insert(format!("a{k}"), a.clone());
        }
        let plan = data.ctor_plan(i);
        let refs = self.run_plan(d, g, phi, &plan, &mut env)?;
        let id = self.has(d, g, phi, t, &target, &format!("rhas.{}", c.symbol), refs);
        Ok(Some(self.retype_has(d, g, phi, t, &target, expected, id)?))
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
        if let Some((data, i)) = data::by_ctor(head)
            && let Some((left, right)) = &data.ctors[i].boundary
        {
            // A path constructor at an endpoint of its interval.
            let n = data.ctors[i].args.len();
            let r = &args[n];
            let dty = self.declared_type(d, g, phi, &data, ty)?;
            for (one, value) in [(false, left), (true, right)] {
                if let Ok(local) = self.f.endpoint(d, phi, r, one) {
                    let value = &value.at(&data, &args[..n]);
                    let pi = self.check(d, g, phi, t, &dty)?;
                    let vi = self.check(d, g, phi, value, &dty)?;
                    let rule = format!("req.{}-{}", data.ctors[i].symbol, u8::from(one));
                    let eq = self.eq(d, g, phi, t, value, &dty, &rule, vec![pi, local, vi]);
                    let eq = self.retype_eq(d, g, phi, t, value, &dty, ty, eq)?;
                    return Ok(Some((value.clone(), ty.clone(), eq)));
                }
            }
            return Ok(None);
        }
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
            && data.ctors[i].boundary.is_some()
        {
            let c = &data.ctors[i];
            let r = &xargs[c.args.len()];
            if self.f.endpoint(d, phi, r, false).is_err()
                && self.f.endpoint(d, phi, r, true).is_err()
            {
                let mut out = methods[i].clone();
                for a in &xargs[..c.args.len()] {
                    out = call("app", [out, a.clone()]);
                }
                for j in c.recursive() {
                    let mut rec = fixed.to_vec();
                    rec.push(xargs[j].clone());
                    out = call("app", [out, call(head, rec)]);
                }
                let out = call("papp", [out, r.clone()]);
                let oi = self.check(d, g, phi, &out, ty)?;
                let rule = format!("req.{}.{}", data.elim, c.symbol);
                let eq = self.eq(d, g, phi, t, &out, ty, &rule, vec![ti, oi]);
                return Ok(Some((out, ty.clone(), eq)));
            }
        } else if let Some((owner, i)) = data::by_ctor(xh)
            && owner.elim == data.elim
        {
            let c = &data.ctors[i];
            let fields = xargs;
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
        if data.is_higher()
            && let ("comp", [family, psi, tube, u]) = (xh, xargs)
            && shape(family)?.0 == data.ty
            && self.f.entails(d, phi, &Face::parse(psi)?).is_err()
        {
            return self
                .eliminate_composition(d, g, phi, t, ty, ti, &data, psi, tube, u)
                .map(Some);
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

    /// The eliminator of a higher inductive type on a formal composition:
    /// composition in the motive along the filler (`req.E.hcomp`).
    #[allow(clippy::too_many_arguments)]
    fn eliminate_composition(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        ty: &Sexp,
        ti: usize,
        data: &Data,
        psi: &Sexp,
        tube: &Sexp,
        u: &Sexp,
    ) -> Result<(Sexp, Sexp, usize)> {
        let (_, args) = shape(t)?;
        let (np, k) = (data.params, data.ctors.len());
        let (params, p, methods) = (&args[..np], &args[np], &args[np + 1..np + 1 + k]);
        // The family must be the parameters weakened by its dimension.
        let mut refs = vec![ti];
        let mut weak = Vec::new();
        for a in params {
            let (b, bi) = self.f.path.transform(a, &Op::DShift(0))?;
            refs.push(bi);
            weak.push(b);
        }
        let family = data::apply(&data.ty, weak.clone());
        if shape(&args[np + 1 + k])?.1[0] != family {
            return Err(format!("{} composed along a varying family", data.name));
        }
        let (fill, fi) = self.filling(&family, &Face::parse(psi)?, tube, u)?;
        let (p1, pi) = self.f.path.transform(p, &Op::DShift(0))?;
        let (pf, si) = self.f.path.transform(&p1, &Op::Subst(0, fill))?;
        refs.extend([fi, pi, si]);
        let mut inner = weak;
        inner.push(p1);
        for m in methods {
            let (m1, mi) = self.f.path.transform(m, &Op::DShift(0))?;
            refs.push(mi);
            inner.push(m1);
        }
        inner.push(tube.clone());
        let mut outer = args[..np + 1 + k].to_vec();
        outer.push(u.clone());
        let out = call(
            "comp",
            [
                pf,
                psi.clone(),
                call(&data.elim, inner),
                call(&data.elim, outer),
            ],
        );
        refs.push(self.check(d, g, phi, &out, ty)?);
        let rule = format!("req.{}.hcomp", data.elim);
        let eq = self.eq(d, g, phi, t, &out, ty, &rule, refs);
        Ok((out, ty.clone(), eq))
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
        if data.is_higher() && data.params == 0 {
            return Ok(None);
        }
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
        for (a, arg_ty) in bargs.iter().zip(&c.args) {
            let line = data.field_type(arg_ty, params);
            parts.push(call("comp", [line, atom("ff"), atom("zero"), a.clone()]));
        }
        // A path constructor stays at its interval.
        parts.extend(bargs[c.args.len()..].iter().cloned());
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
            let eq = self.eq(
                d,
                g,
                phi,
                a,
                b,
                &u(0),
                &format!("req.{}-cong", data.ty),
                refs,
            );
            return Ok(Some(self.retype_eq(d, g, phi, a, b, &u(0), ty, eq)?));
        }
        if let Some((data, i)) = data::by_ctor(ah)
            && data.ctors[i].boundary.is_some()
        {
            let c = &data.ctors[i];
            let n = c.args.len();
            let dty = self.declared_type(d, g, phi, &data, ty)?;
            let params = shape(&dty)?.1.to_vec();
            let mut refs = Vec::new();
            for (x, (y, arg_ty)) in ax[..n].iter().zip(bx[..n].iter().zip(&c.args)) {
                let field_ty = data.field_type(arg_ty, &params);
                refs.push(self.equality(d, g, phi, x, y, &field_ty)?);
            }
            refs.push(self.check(d, g, phi, a, &dty)?);
            refs.push(self.local_interval(d, phi, &ax[n], &bx[n])?);
            refs.push(self.f.path.interval(d, &bx[n])?);
            let rule = format!("req.{}-cong", c.symbol);
            let eq = self.eq(d, g, phi, a, b, &dty, &rule, refs);
            return Ok(Some(self.retype_eq(d, g, phi, a, b, &dty, ty, eq)?));
        }
        if let Some((data, i)) = data::by_ctor(ah) {
            let c = &data.ctors[i];
            // The parameters come from the type the equation is stated at.
            let (th, params) = shape(ty)?;
            if c.args.is_empty() || th != data.ty {
                return Ok(None);
            }
            let mut refs = Vec::new();
            for ((x, y), arg_ty) in ax.iter().zip(bx).zip(&c.args) {
                let field_ty = data.field_type(arg_ty, params);
                refs.push(self.equality(d, g, phi, x, y, &field_ty)?);
            }
            let dty = ty.clone();
            let eq = self.eq(
                d,
                g,
                phi,
                a,
                b,
                &dty,
                &format!("req.{}-cong", c.symbol),
                refs,
            );
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
            let eq = self.eq(
                d,
                g,
                phi,
                w,
                &out,
                &u(0),
                &format!("req.{}-cong", data.ty),
                refs,
            );
            let eq = self.retype_eq(d, g, phi, w, &out, &u(0), ty, eq)?;
            return Ok(Some((out, eq)));
        }
        let (th, params) = shape(ty)?;
        let Some((data, i)) = data::by_ctor(head) else {
            return Ok(None);
        };
        let c = &data.ctors[i];
        if c.args.is_empty() || c.boundary.is_some() || th != data.ty {
            return Ok(None);
        }
        let (mut out, mut refs, mut changed) = (Vec::new(), Vec::new(), false);
        for (a, arg_ty) in args.iter().zip(&c.args) {
            let field_ty = data.field_type(arg_ty, params);
            let (av, ea) = self.value(d, g, phi, a, &field_ty, fuel)?;
            changed |= av != *a;
            out.push(av);
            refs.push(ea);
        }
        if !changed {
            return Ok(None);
        }
        let out = call(head, out);
        let eq = self.eq(
            d,
            g,
            phi,
            w,
            &out,
            ty,
            &format!("req.{}-cong", c.symbol),
            refs,
        );
        Ok(Some((out, eq)))
    }
}
