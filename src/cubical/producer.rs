//! Bounded, untrusted producer for existing scoped cubical fragments. Every
//! substitution and typing operation emits evidence for the ground kernel.
mod composition;
mod congruence;
mod definitions;
mod faces;
mod glue;
mod restricted;
mod sigma;
mod syntax;
mod systems;

use super::ast::{Definition, Face, Interval, Term, context, extend, number};
use crate::sexp::{Result, Sexp, call};
use std::collections::BTreeMap;
use std::fmt::Write as _;

pub const THEORY: &str = include_str!("../../theories/cubical/path.horn");
const MAX_STEPS: usize = 50_000;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub enum Profile {
    #[default]
    Path,
    Faces,
    Systems,
    Composition,
    Sigma,
    Equivalence,
    Glue,
    Equality,
}

impl Profile {
    fn fragments(self) -> usize {
        match self {
            Self::Path => 1,
            Self::Faces => 2,
            Self::Systems => 5,
            Self::Composition => 6,
            Self::Sigma => 7,
            Self::Equivalence => 8,
            Self::Glue => 9,
            Self::Equality => 10,
        }
    }

    pub fn parse(name: &str) -> Result<Self> {
        match name {
            "path" => Ok(Self::Path),
            "faces" => Ok(Self::Faces),
            "systems" => Ok(Self::Systems),
            "composition" => Ok(Self::Composition),
            "sigma" => Ok(Self::Sigma),
            "equivalence" => Ok(Self::Equivalence),
            "glue" => Ok(Self::Glue),
            "equality" => Ok(Self::Equality),
            _ => Err(format!("unknown fixed cubical profile {name}")),
        }
    }

    pub fn theory(self) -> String {
        super::FRAGMENTS[..self.fragments()]
            .iter()
            .map(|(_, source)| format!("{source}\n"))
            .collect()
    }
}

#[derive(Clone)]
enum Op {
    Shift(usize),
    Subst(usize, Term),
    DShift(usize),
    DSubst(usize, Interval),
}

impl Op {
    fn prefix(&self) -> &'static str {
        match self {
            Self::Shift(_) => "shift",
            Self::Subst(..) => "subst",
            Self::DShift(_) => "dshift",
            Self::DSubst(..) => "dsubst",
        }
    }
    fn cutoff(&self) -> usize {
        match self {
            Self::Shift(k) | Self::Subst(k, _) | Self::DShift(k) | Self::DSubst(k, _) => *k,
        }
    }
}

type InferenceKey = (usize, Vec<Term>, Term);
type RestrictedInferenceKey = (usize, Vec<Term>, Face, Term);

#[derive(Default)]
struct Producer {
    profile: Profile,
    reduction_depth: usize,
    steps: Vec<(String, Vec<usize>, Sexp)>,
    known: BTreeMap<Sexp, usize>,
    inferred: BTreeMap<InferenceKey, (Term, usize)>,
    restricted_inferred: BTreeMap<RestrictedInferenceKey, (Term, usize)>,
    conversion_depth: usize,
    face_work: usize,
    restricted_depth: usize,
}

impl Producer {
    fn emit(&mut self, rule: &str, refs: Vec<usize>, judgment: Sexp) -> Result<usize> {
        if let Some(&id) = self.known.get(&judgment) {
            return Ok(id);
        }
        if self.steps.len() >= MAX_STEPS {
            return Err("cubical producer exceeded its 50000-step limit".into());
        }
        let id = self.steps.len();
        self.known.insert(judgment.clone(), id);
        self.steps.push((rule.to_owned(), refs, judgment));
        Ok(id)
    }

    fn fact(&mut self, rule: &str, refs: Vec<usize>, pred: &str, args: Vec<Sexp>) -> Result<usize> {
        self.emit(rule, refs, call(pred, args))
    }

    fn comparison(&mut self, m: usize, n: usize, strict: bool) -> Result<usize> {
        let pred = if strict { "lt" } else { "le" };
        if (strict && m >= n) || (!strict && m > n) {
            return Err(format!("invalid comparison {m} {pred} {n}"));
        }
        let (suffix, refs) = if m == 0 {
            ("z", vec![])
        } else {
            ("s", vec![self.comparison(m - 1, n - 1, strict)?])
        };
        self.fact(
            &format!("{pred}.{suffix}"),
            refs,
            pred,
            vec![number(m), number(n)],
        )
    }

    fn max(&mut self, m: usize, n: usize) -> Result<usize> {
        let (suffix, refs) = if m == 0 {
            ("z", vec![])
        } else if n == 0 {
            ("sz", vec![])
        } else {
            ("ss", vec![self.max(m - 1, n - 1)?])
        };
        self.fact(
            &format!("max.{suffix}"),
            refs,
            "max",
            vec![number(m), number(n), number(m.max(n))],
        )
    }

    /// Lift an operation across one ordinary or dimension binder. Ordinary
    /// substitution crossing dimensions must lift dimensions in its replacement.
    fn under(&mut self, op: &Op, dimension: bool, refs: &mut Vec<usize>) -> Result<Op> {
        Ok(match (op, dimension) {
            (Op::Shift(k), false) => Op::Shift(k + 1),
            (Op::Subst(k, r), false) => {
                let (r, id) = self.transform(r, &Op::Shift(0))?;
                refs.push(id);
                Op::Subst(k + 1, r)
            }
            (Op::Subst(k, r), true) => {
                let (r, id) = self.transform(r, &Op::DShift(0))?;
                refs.push(id);
                Op::Subst(*k, r)
            }
            (Op::DShift(k), true) => Op::DShift(k + 1),
            (Op::DSubst(k, r), true) => {
                let (r, id) = self.itransform(r, 0, None, true)?;
                refs.push(id);
                Op::DSubst(k + 1, r)
            }
            _ => op.clone(),
        })
    }

    // `shift` selects interval shifting; otherwise substitute at k.
    fn itransform(
        &mut self,
        r: &Interval,
        k: usize,
        replacement: Option<&Interval>,
        shift: bool,
    ) -> Result<(Interval, usize)> {
        use Interval::*;
        let mut refs = Vec::new();
        let (out, suffix) = match r {
            Zero => (Zero, "0"),
            One => (One, "1"),
            Var(n) if !shift && *n == k => (replacement.unwrap().clone(), "dim.hit"),
            Var(n) if *n < k => {
                refs.push(self.comparison(*n, k, true)?);
                (Var(*n), "dim.lt")
            }
            Var(n) if shift => {
                refs.push(self.comparison(k, *n, false)?);
                (Var(n + 1), "dim.ge")
            }
            Var(n) => {
                refs.push(self.comparison(k, *n, true)?);
                (Var(n - 1), "dim.gt")
            }
            Neg(a) => {
                let (a, id) = self.itransform(a, k, replacement, shift)?;
                refs.push(id);
                (Neg(Box::new(a)), "neg")
            }
            Meet(a, b) | Join(a, b) => {
                let (a, x) = self.itransform(a, k, replacement, shift)?;
                let (b, y) = self.itransform(b, k, replacement, shift)?;
                refs.extend([x, y]);
                if matches!(r, Meet(..)) {
                    (Meet(Box::new(a), Box::new(b)), "meet")
                } else {
                    (Join(Box::new(a), Box::new(b)), "join")
                }
            }
        };
        let pred = if shift { "ishift" } else { "isubst" };
        let mut args = vec![r.quote(), number(k)];
        if !shift {
            args.push(replacement.unwrap().quote());
        }
        args.push(out.quote());
        let id = self.fact(&format!("{pred}.{suffix}"), refs, pred, args)?;
        Ok((out, id))
    }

    fn transform(&mut self, t: &Term, op: &Op) -> Result<(Term, usize)> {
        use Term::*;
        let k = op.cutoff();
        let mut refs = Vec::new();
        let (out, suffix) = match t {
            Defined(_) => return Err("unexpanded definition reached the core producer".into()),
            Universe(l) => (Universe(*l), "u"),
            Nat => (Nat, "nat"),
            Zero => (Zero, "zero"),
            Var(n) => match op {
                Op::DShift(_) | Op::DSubst(..) => (Var(*n), "v"),
                Op::Subst(_, r) if *n == k => (r.clone(), "v.hit"),
                _ if *n < k => {
                    refs.push(self.comparison(*n, k, true)?);
                    (Var(*n), "v.lt")
                }
                Op::Shift(_) => {
                    refs.push(self.comparison(k, *n, false)?);
                    (Var(n + 1), "v.ge")
                }
                _ => {
                    refs.push(self.comparison(k, *n, true)?);
                    (Var(n - 1), "v.gt")
                }
            },
            Pi(a, b) | Sigma(a, b) => {
                let (a, id) = self.transform(a, op)?;
                refs.push(id);
                let inner = self.under(op, false, &mut refs)?;
                let (b, id) = self.transform(b, &inner)?;
                refs.push(id);
                (
                    if matches!(t, Pi(..)) {
                        Pi(Box::new(a), Box::new(b))
                    } else {
                        Sigma(Box::new(a), Box::new(b))
                    },
                    if matches!(t, Pi(..)) { "pi" } else { "sigma" },
                )
            }
            Lam(a, b) => {
                // Domain is source metadata, absent from the quoted lambda.
                let (a, _) = self.transform(a, op)?;
                let inner = self.under(op, false, &mut refs)?;
                let (b, id) = self.transform(b, &inner)?;
                refs.push(id);
                (Lam(Box::new(a), Box::new(b)), "lam")
            }
            Pair(ty, a, b) => {
                let (ty, _) = self.transform(ty, op)?;
                let (a, x) = self.transform(a, op)?;
                let (b, y) = self.transform(b, op)?;
                refs.extend([x, y]);
                (Pair(Box::new(ty), Box::new(a), Box::new(b)), "pair")
            }
            Fst(p) | Snd(p) => {
                let (p, x) = self.transform(p, op)?;
                refs.push(x);
                (
                    if matches!(t, Fst(..)) {
                        Fst(Box::new(p))
                    } else {
                        Snd(Box::new(p))
                    },
                    if matches!(t, Fst(..)) { "fst" } else { "snd" },
                )
            }
            GlueType(a, phi, t, e) => {
                let (a, x) = self.transform(a, op)?;
                refs.push(x);
                let phi = if matches!(op, Op::DShift(_) | Op::DSubst(..)) {
                    let (phi, id) = self.transform_face(phi, op)?;
                    refs.push(id);
                    phi
                } else {
                    phi.clone()
                };
                let (t, y) = self.transform(t, op)?;
                let (e, z) = self.transform(e, op)?;
                refs.extend([y, z]);
                (
                    GlueType(Box::new(a), phi, Box::new(t), Box::new(e)),
                    "glue-type",
                )
            }
            Glue(g, u, v) => {
                let (g, x) = self.transform(g, op)?;
                let (u, y) = self.transform(u, op)?;
                let (v, z) = self.transform(v, op)?;
                refs.extend([x, y, z]);
                (Glue(Box::new(g), Box::new(u), Box::new(v)), "glue")
            }
            Unglue(u) => {
                let (u, x) = self.transform(u, op)?;
                refs.push(x);
                (Unglue(Box::new(u)), "unglue")
            }
            App(f, a) => {
                let (f, x) = self.transform(f, op)?;
                let (a, y) = self.transform(a, op)?;
                refs.extend([x, y]);
                (App(Box::new(f), Box::new(a)), "app")
            }
            Path(a, b, c) => {
                let inner = self.under(op, true, &mut refs)?;
                let (a, x) = self.transform(a, &inner)?;
                let (b, y) = self.transform(b, op)?;
                let (c, z) = self.transform(c, op)?;
                refs.extend([x, y, z]);
                (Path(Box::new(a), Box::new(b), Box::new(c)), "path")
            }
            PathLam(a, body) => {
                let inner = self.under(op, true, &mut refs)?;
                let (a, _) = self.transform(a, &inner)?;
                let (body, id) = self.transform(body, &inner)?;
                refs.push(id);
                (PathLam(Box::new(a), Box::new(body)), "plam")
            }
            Comp(a, phi, tube, base) => {
                let inner = self.under(op, true, &mut refs)?;
                let (a, x) = self.transform(a, &inner)?;
                refs.push(x);
                let phi = if matches!(op, Op::DShift(_) | Op::DSubst(..)) {
                    let (phi, id) = self.transform_face(phi, op)?;
                    refs.push(id);
                    phi
                } else {
                    phi.clone()
                };
                let (tube, y) = self.transform(tube, &inner)?;
                let (base, z) = self.transform(base, op)?;
                refs.extend([y, z]);
                (
                    Comp(Box::new(a), phi, Box::new(tube), Box::new(base)),
                    "comp",
                )
            }
            System(ty, sides) => {
                let (ty, _) = self.transform(ty, op)?;
                let (sides, id) = self.transform_system(sides, op)?;
                refs.push(id);
                (System(Box::new(ty), sides), "system")
            }
            PathApp(p, r) => {
                let (p, id) = self.transform(p, op)?;
                refs.push(id);
                let r = match op {
                    Op::DShift(_) | Op::DSubst(..) => {
                        let replacement = if let Op::DSubst(_, r) = op {
                            Some(r)
                        } else {
                            None
                        };
                        let (r, id) =
                            self.itransform(r, k, replacement, matches!(op, Op::DShift(_)))?;
                        refs.push(id);
                        r
                    }
                    _ => r.clone(),
                };
                (PathApp(Box::new(p), r), "papp")
            }
        };
        let pred = op.prefix();
        let mut args = vec![t.quote(), number(k)];
        match op {
            Op::Subst(_, r) => args.push(r.quote()),
            Op::DSubst(_, r) => args.push(r.quote()),
            _ => {}
        }
        args.push(out.quote());
        let id = self.fact(&format!("{pred}.{suffix}"), refs, pred, args)?;
        Ok((out, id))
    }

    fn dshiftctx(&mut self, g: &[Term]) -> Result<(Vec<Term>, usize)> {
        let Some((a, prefix)) = g.split_last() else {
            return Ok((
                Vec::new(),
                self.fact(
                    "dshiftctx.nil",
                    vec![],
                    "dshiftctx",
                    vec![context(g), number(0), context(g)],
                )?,
            ));
        };
        let (g2, tail) = self.dshiftctx(prefix)?;
        let (a2, head) = self.transform(a, &Op::DShift(0))?;
        let out = extend(&g2, &a2);
        let id = self.fact(
            "dshiftctx.cons",
            vec![tail, head],
            "dshiftctx",
            vec![context(g), number(0), context(&out)],
        )?;
        Ok((out, id))
    }

    fn interval(&mut self, d: usize, r: &Interval) -> Result<usize> {
        use Interval::*;
        let (suffix, refs) = match r {
            Zero => ("0", vec![]),
            One => ("1", vec![]),
            Var(n) => ("dim", vec![self.comparison(*n, d, true)?]),
            Neg(a) => ("neg", vec![self.interval(d, a)?]),
            Meet(a, b) | Join(a, b) => {
                let refs = vec![self.interval(d, a)?, self.interval(d, b)?];
                (
                    if matches!(r, Meet(..)) {
                        "meet"
                    } else {
                        "join"
                    },
                    refs,
                )
            }
        };
        self.fact(
            &format!("interval.{suffix}"),
            refs,
            "interval",
            vec![number(d), r.quote()],
        )
    }

    fn ctx(&mut self, d: usize, g: &[Term]) -> Result<usize> {
        let key = call("ctx", [number(d), context(g)]);
        if let Some(&id) = self.known.get(&key) {
            return Ok(id);
        }
        let (rule, refs) = match g.split_last() {
            None => ("ctx.nil", vec![]),
            Some((a, prefix)) => {
                let tail = self.ctx(d, prefix)?;
                let (_, head) = self.universe(d, prefix, a)?;
                ("ctx.cons", vec![tail, head])
            }
        };
        self.emit(rule, refs, key)
    }

    fn lookup(&mut self, g: &[Term], n: usize) -> Result<(Term, usize)> {
        let (a, prefix) = g
            .split_last()
            .ok_or_else(|| format!("unbound variable {n}"))?;
        let (ty, refs, rule) = if n == 0 {
            let (ty, id) = self.transform(a, &Op::Shift(0))?;
            (ty, vec![id], "lookup.z")
        } else {
            let (ty, x) = self.lookup(prefix, n - 1)?;
            let (ty, y) = self.transform(&ty, &Op::Shift(0))?;
            (ty, vec![x, y], "lookup.s")
        };
        let id = self.fact(
            rule,
            refs,
            "lookup",
            vec![context(g), number(n), ty.quote()],
        )?;
        Ok((ty, id))
    }

    fn has(
        &mut self,
        rule: &str,
        refs: Vec<usize>,
        d: usize,
        g: &[Term],
        t: &Term,
        ty: &Term,
    ) -> Result<usize> {
        self.fact(
            rule,
            refs,
            "has",
            vec![number(d), context(g), t.quote(), ty.quote()],
        )
    }

    fn converting<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        if self.conversion_depth >= 32 {
            return Err("cubical conversion exceeded its nesting limit of 32".into());
        }
        self.conversion_depth += 1;
        let result = f(self);
        self.conversion_depth -= 1;
        result
    }

    /// Expose a reducible type head and explicitly transport the subject's
    /// typing judgment with the existing type.conv rule.
    fn expose(
        &mut self,
        d: usize,
        g: &[Term],
        t: &Term,
        ty: &Term,
        typed: usize,
    ) -> Result<(Term, usize)> {
        let (level, _) = self.universe(d, g, ty)?;
        let kind = Term::Universe(level);
        let (normal, equality) = self.normalize(d, g, ty, &kind)?;
        if normal.quote() == ty.quote() {
            return Ok((normal, typed));
        }
        let well_formed = self.check(d, g, &normal, &kind)?;
        let converted = self.has(
            "type.conv",
            vec![typed, equality, well_formed],
            d,
            g,
            t,
            &normal,
        )?;
        Ok((normal, converted))
    }

    fn universe(&mut self, d: usize, g: &[Term], t: &Term) -> Result<(usize, usize)> {
        let (ty, id) = self.infer(d, g, t)?;
        if let Term::Universe(l) = ty {
            return Ok((l, id));
        }
        self.converting(|p| {
            let (normal, id) = p.expose(d, g, t, &ty, id)?;
            if let Term::Universe(l) = normal {
                Ok((l, id))
            } else {
                Err(format!(
                    "expected a type, got {} : {}",
                    t.quote(),
                    normal.quote()
                ))
            }
        })
    }

    fn check(&mut self, d: usize, g: &[Term], t: &Term, expected: &Term) -> Result<usize> {
        let (actual, id) = self.infer(d, g, t)?;
        if actual.quote() == expected.quote() {
            return Ok(id);
        }
        self.converting(|p| {
            let (i, _) = p.universe(d, g, &actual)?;
            let (j, well_formed) = p.universe(d, g, expected)?;
            if i != j {
                return Err(
                    "type conversion requires the same universe level; no cumulativity".into(),
                );
            }
            let equality = p
                .equal(d, g, &actual, expected, &Term::Universe(i))
                .map_err(|e| {
                    format!(
                        "type mismatch: inferred {}, expected {}; conversion failed: {e}",
                        actual.quote(),
                        expected.quote()
                    )
                })?;
            p.has(
                "type.conv",
                vec![id, equality, well_formed],
                d,
                g,
                t,
                expected,
            )
        })
    }

    fn infer(&mut self, d: usize, g: &[Term], t: &Term) -> Result<(Term, usize)> {
        use Term::*;
        let key = (d, g.to_vec(), t.clone());
        if let Some(out) = self.inferred.get(&key) {
            return Ok(out.clone());
        }
        let (ty, refs, rule) = match t {
            Defined(_) => return Err("unexpanded definition reached the core producer".into()),
            Universe(l) => (Universe(l + 1), vec![self.ctx(d, g)?], "type.u"),
            Nat => (Universe(0), vec![self.ctx(d, g)?], "type.nat"),
            Zero => (Nat, vec![self.ctx(d, g)?], "type.zero"),
            Var(n) => {
                let ctx = self.ctx(d, g)?;
                let (ty, lookup) = self.lookup(g, *n)?;
                (ty, vec![ctx, lookup], "type.v")
            }
            Pi(a, b) => {
                let (i, x) = self.universe(d, g, a)?;
                let (j, y) = self.universe(d, &extend(g, a), b)?;
                let z = self.max(i, j)?;
                (Universe(i.max(j)), vec![x, y, z], "type.pi")
            }
            Lam(a, body) => {
                let (_, x) = self.universe(d, g, a)?;
                let inner = extend(g, a);
                let (b, y) = self.infer(d, &inner, body)?;
                let (_, z) = self.universe(d, &inner, &b)?;
                (Pi(a.clone(), Box::new(b)), vec![x, y, z], "type.lam")
            }
            App(f, a) => {
                let (mut fty, mut x) = self.infer(d, g, f)?;
                if !matches!(fty, Pi(..)) {
                    (fty, x) = self.converting(|p| p.expose(d, g, f, &fty, x))?;
                }
                let Pi(domain, codomain) = fty else {
                    return Err("application requires a function".into());
                };
                let y = self.check(d, g, a, &domain)?;
                let (out, z) = self.transform(&codomain, &Op::Subst(0, *a.clone()))?;
                (out, vec![x, y, z], "type.app")
            }
            Path(a, b, c) => {
                let ctx = self.ctx(d, g)?;
                let (inner, shifted) = self.dshiftctx(g)?;
                let (l, family) = self.universe(d + 1, &inner, a)?;
                let (a0, x) = self.transform(a, &Op::DSubst(0, Interval::Zero))?;
                let (a1, y) = self.transform(a, &Op::DSubst(0, Interval::One))?;
                let b = self.check(d, g, b, &a0)?;
                let c = self.check(d, g, c, &a1)?;
                (
                    Universe(l),
                    vec![ctx, shifted, family, x, y, b, c],
                    "type.path",
                )
            }
            PathLam(a, body) => {
                let ctx = self.ctx(d, g)?;
                let (inner, shifted) = self.dshiftctx(g)?;
                let (_, family) = self.universe(d + 1, &inner, a)?;
                let body_id = self.check(d + 1, &inner, body, a)?;
                let (a0, x) = self.transform(a, &Op::DSubst(0, Interval::Zero))?;
                let (a1, y) = self.transform(a, &Op::DSubst(0, Interval::One))?;
                let (t0, z) = self.transform(body, &Op::DSubst(0, Interval::Zero))?;
                let (t1, w) = self.transform(body, &Op::DSubst(0, Interval::One))?;
                let b = self.check(d, g, &t0, &a0)?;
                let c = self.check(d, g, &t1, &a1)?;
                (
                    Path(a.clone(), Box::new(t0), Box::new(t1)),
                    vec![ctx, shifted, family, body_id, x, y, z, w, b, c],
                    "type.plam",
                )
            }
            Sigma(..) | Pair(..) | Fst(..) | Snd(..) => {
                let (ty, restricted) = self.sigma_infer((d, g), &Face::True, t)?;
                (ty, vec![restricted], "rhas.export")
            }
            GlueType(..) | Glue(..) | Unglue(..) => {
                let (ty, restricted) = self.glue_infer((d, g), &Face::True, t)?;
                (ty, vec![restricted], "rhas.export")
            }
            Comp(..) => {
                let (ty, restricted) = self.composition_has((d, g), &Face::True, t)?;
                (ty, vec![restricted], "rhas.export")
            }
            System(ty, sides) => {
                let restricted = self.system_has(d, g, &Face::True, sides, ty)?;
                (*ty.clone(), vec![restricted], "rhas.export")
            }
            PathApp(p, r) => {
                let (mut pty, mut x) = self.infer(d, g, p)?;
                if !matches!(pty, Path(..)) {
                    (pty, x) = self.converting(|producer| producer.expose(d, g, p, &pty, x))?;
                }
                let Path(a, _, _) = pty else {
                    return Err("path application requires a path".into());
                };
                let y = self.interval(d, r)?;
                let (out, z) = self.transform(&a, &Op::DSubst(0, r.clone()))?;
                let (_, u) = self.universe(d, g, &out)?;
                (out, vec![x, y, z, u], "type.papp")
            }
        };
        let id = self.has(rule, refs, d, g, t, &ty)?;
        self.inferred.insert(key, (ty.clone(), id));
        Ok((ty, id))
    }
}

impl Producer {
    fn equality_step(
        &mut self,
        rule: &str,
        refs: Vec<usize>,
        scope: (usize, &[Term]),
        a: &Term,
        b: &Term,
        ty: &Term,
    ) -> Result<usize> {
        let (d, g) = scope;
        self.fact(
            rule,
            refs,
            "eq",
            vec![number(d), context(g), a.quote(), b.quote(), ty.quote()],
        )
    }

    fn reduce(&mut self, d: usize, g: &[Term], t: &Term) -> Result<Option<(Term, usize)>> {
        use Term::*;
        match t {
            Comp(..) | Fst(..) | Snd(..) | GlueType(..) | Glue(..) | Unglue(..) => {
                let Some((out, ty, step)) = self.restricted_reduce((d, g), &Face::True, t)? else {
                    return Ok(None);
                };
                let id = self.equality_step("req.export", vec![step], (d, g), t, &out, &ty)?;
                Ok(Some((out, id)))
            }
            System(ty, sides) => self.reduce_system(d, g, sides, ty),
            App(f, r) if matches!(f.as_ref(), Lam(..)) => {
                let Lam(a, body) = f.as_ref() else {
                    unreachable!()
                };
                let (_, x) = self.universe(d, g, a)?;
                let inner = extend(g, a);
                let (b, y) = self.infer(d, &inner, body)?;
                let (_, z) = self.universe(d, &inner, &b)?;
                let arg = self.check(d, g, r, a)?;
                let (out, sub) = self.transform(body, &Op::Subst(0, *r.clone()))?;
                let (ty, sub_ty) = self.transform(&b, &Op::Subst(0, *r.clone()))?;
                let id = self.equality_step(
                    "eq.beta",
                    vec![x, y, z, arg, sub, sub_ty],
                    (d, g),
                    t,
                    &out,
                    &ty,
                )?;
                Ok(Some((out, id)))
            }
            PathApp(p, r) => {
                let (mut pty, mut path_id) = self.infer(d, g, p)?;
                if !matches!(pty, Path(..)) {
                    (pty, path_id) =
                        self.converting(|producer| producer.expose(d, g, p, &pty, path_id))?;
                }
                let Path(a, b, c) = pty else {
                    return Err("path application requires a path".into());
                };
                let (ty, sub_ty) = self.transform(&a, &Op::DSubst(0, r.clone()))?;
                if let PathLam(_, body) = p.as_ref() {
                    let dim = self.interval(d, r)?;
                    let (out, sub) = self.transform(body, &Op::DSubst(0, r.clone()))?;
                    let typed = self.check(d, g, &out, &ty)?;
                    let id = self.equality_step(
                        "eq.pbeta",
                        vec![path_id, dim, sub_ty, sub, typed],
                        (d, g),
                        t,
                        &out,
                        &ty,
                    )?;
                    Ok(Some((out, id)))
                } else if matches!(r, Interval::Zero | Interval::One) {
                    let out = if *r == Interval::Zero { *b } else { *c };
                    let typed = self.check(d, g, &out, &ty)?;
                    let rule = if *r == Interval::Zero {
                        "eq.p0"
                    } else {
                        "eq.p1"
                    };
                    let id = self.equality_step(
                        rule,
                        vec![path_id, sub_ty, typed],
                        (d, g),
                        t,
                        &out,
                        &ty,
                    )?;
                    Ok(Some((out, id)))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    fn normalize(&mut self, d: usize, g: &[Term], t: &Term, ty: &Term) -> Result<(Term, usize)> {
        let typed = self.check(d, g, t, ty)?;
        let mut evidence = self.equality_step("eq.refl", vec![typed], (d, g), t, t, ty)?;
        let mut current = t.clone();
        for reductions in 0..=32 {
            let Some((out, step)) = self.reduce(d, g, &current)? else {
                return Ok((current, evidence));
            };
            if reductions == 32 {
                return Err("cubical equality exceeded its 32 root-reduction limit".into());
            }
            // This small theory has type.conv but no general eq.conv. Never
            // pretend that equalities at convertible types are identical.
            let step_type = self.steps[step]
                .2
                .list()?
                .last()
                .ok_or("missing equality type")?;
            if step_type != &ty.quote() {
                return Err("equality reduction at a converted type is not supported by the scoped-path producer".into());
            }
            self.check(d, g, &out, ty)?;
            evidence = self.equality_step("eq.trans", vec![evidence, step], (d, g), t, &out, ty)?;
            current = out;
        }
        unreachable!("bounded reductions return or report their limit")
    }

    fn equal(&mut self, d: usize, g: &[Term], a: &Term, b: &Term, ty: &Term) -> Result<usize> {
        let typed = self.check(d, g, a, ty)?;
        self.check(d, g, b, ty)?;
        if a.quote() == b.quote() {
            return self.equality_step("eq.refl", vec![typed], (d, g), a, b, ty);
        }
        let (left, l) = self.normalize(d, g, a, ty)?;
        let (right, r) = self.normalize(d, g, b, ty)?;
        if left.quote() != right.quote() {
            return Err(
                "equality not established by reflexivity and root beta/path reduction".into(),
            );
        }
        let reverse = self.equality_step("eq.sym", vec![r], (d, g), &right, b, ty)?;
        self.equality_step("eq.trans", vec![l, reverse], (d, g), a, b, ty)
    }
}

impl Producer {
    fn request_ctx(&mut self, d: usize, g: &[Term]) -> Result<usize> {
        if self.profile < Profile::Equality {
            return self.ctx(d, g);
        }
        let local = self.restricted_ctx(d, g, &Face::True)?;
        self.fact(
            "rctx.export",
            vec![local],
            "ctx",
            vec![number(d), context(g)],
        )
    }

    fn request_universe(&mut self, d: usize, g: &[Term], t: &Term) -> Result<(usize, usize)> {
        if self.profile < Profile::Equality {
            return self.universe(d, g, t);
        }
        let (level, restricted) = self.restricted_universe(d, g, &Face::True, t)?;
        let id = self.has(
            "rhas.export",
            vec![restricted],
            d,
            g,
            t,
            &Term::Universe(level),
        )?;
        Ok((level, id))
    }

    fn request_check(&mut self, d: usize, g: &[Term], t: &Term, ty: &Term) -> Result<usize> {
        if self.profile < Profile::Equality {
            return self.check(d, g, t, ty);
        }
        let restricted = self.restricted_check(d, g, &Face::True, t, ty)?;
        self.has("rhas.export", vec![restricted], d, g, t, ty)
    }
}

/// Context types are stored oldest first, at their binding site. Ordinary
/// variables and dimension variables are independent de Bruijn namespaces.
#[derive(Clone, Debug)]
pub struct Request {
    pub name: String,
    pub dimensions: usize,
    pub context: Vec<Term>,
    pub judgment: Judgment,
}

#[derive(Clone, Debug)]
pub enum Judgment {
    Definition {
        definition: Definition,
        expansion: Term,
    },
    Has {
        term: Term,
        ty: Term,
    },
    Equal {
        left: Term,
        right: Term,
        ty: Term,
    },
    Entails {
        premise: Face,
        conclusion: Face,
    },
    Local {
        face: Face,
        left: Interval,
        right: Interval,
    },
    RestrictedHas {
        face: Face,
        term: Term,
        ty: Term,
    },
    RestrictedEqual {
        face: Face,
        left: Term,
        right: Term,
        ty: Term,
    },
}

pub struct Generated {
    pub profile: Profile,
    pub theory: String,
    pub goals: String,
    pub proof: String,
    pub checked: crate::kernel::Report,
}

/// Validate producer syntax before recursive inference/quotation. These are
/// resource bounds, not new logical premises or claims of completeness.
fn validate(request: &Request) -> Result<()> {
    use syntax::{face, interval, term};
    if request.dimensions > 32 || request.context.len() > 32 {
        return Err("scope exceeds 32 variables or dimensions".into());
    }
    if request.name.is_empty()
        || !request
            .name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '.'))
    {
        return Err("goal names must contain only ASCII letters, digits, _, - or .".into());
    }
    let mut nodes = 0;
    for a in &request.context {
        term(a, 0, &mut nodes)?;
    }
    match &request.judgment {
        Judgment::Has { term: t, ty } => {
            term(t, 0, &mut nodes)?;
            term(ty, 0, &mut nodes)?;
        }
        Judgment::Equal { left, right, ty } => {
            term(left, 0, &mut nodes)?;
            term(right, 0, &mut nodes)?;
            term(ty, 0, &mut nodes)?;
        }
        Judgment::Entails {
            premise,
            conclusion,
        } => {
            face(premise, 0, &mut nodes)?;
            face(conclusion, 0, &mut nodes)?;
        }
        Judgment::Local {
            face: phi,
            left,
            right,
        } => {
            face(phi, 0, &mut nodes)?;
            interval(left, 0, &mut nodes)?;
            interval(right, 0, &mut nodes)?;
        }
        Judgment::RestrictedHas {
            face: phi,
            term: t,
            ty,
        } => {
            face(phi, 0, &mut nodes)?;
            term(t, 0, &mut nodes)?;
            term(ty, 0, &mut nodes)?;
        }
        Judgment::RestrictedEqual {
            face: phi,
            left,
            right,
            ty,
        } => {
            face(phi, 0, &mut nodes)?;
            term(left, 0, &mut nodes)?;
            term(right, 0, &mut nodes)?;
            term(ty, 0, &mut nodes)?;
        }
        Judgment::Definition {
            definition,
            expansion,
        } => {
            for arg in definition.arguments() {
                term(arg, 0, &mut nodes)?;
            }
            term(expansion, 0, &mut nodes)?;
        }
    }
    Ok(())
}

fn needs_systems(request: &Request) -> bool {
    if request.context.iter().any(Term::has_system) {
        return true;
    }
    match &request.judgment {
        Judgment::RestrictedHas { .. } | Judgment::RestrictedEqual { .. } => true,
        Judgment::Has { term, ty } => term.has_system() || ty.has_system(),
        Judgment::Equal { left, right, ty } => {
            left.has_system() || right.has_system() || ty.has_system()
        }
        _ => false,
    }
}

fn needs_composition(request: &Request) -> bool {
    if request.context.iter().any(Term::has_composition) {
        return true;
    }
    match &request.judgment {
        Judgment::Has { term, ty } | Judgment::RestrictedHas { term, ty, .. } => {
            term.has_composition() || ty.has_composition()
        }
        Judgment::Equal { left, right, ty }
        | Judgment::RestrictedEqual {
            left, right, ty, ..
        } => left.has_composition() || right.has_composition() || ty.has_composition(),
        _ => false,
    }
}

fn needs_sigma(request: &Request) -> bool {
    if request.context.iter().any(Term::has_sigma) {
        return true;
    }
    match &request.judgment {
        Judgment::Has { term, ty } | Judgment::RestrictedHas { term, ty, .. } => {
            term.has_sigma() || ty.has_sigma()
        }
        Judgment::Equal { left, right, ty }
        | Judgment::RestrictedEqual {
            left, right, ty, ..
        } => left.has_sigma() || right.has_sigma() || ty.has_sigma(),
        _ => false,
    }
}

fn needs_equivalence(request: &Request) -> bool {
    if request.context.iter().any(Term::has_definition) {
        return true;
    }
    match &request.judgment {
        Judgment::Definition { .. } => true,
        Judgment::Has { term, ty } | Judgment::RestrictedHas { term, ty, .. } => {
            term.has_definition() || ty.has_definition()
        }
        Judgment::Equal { left, right, ty }
        | Judgment::RestrictedEqual {
            left, right, ty, ..
        } => left.has_definition() || right.has_definition() || ty.has_definition(),
        _ => false,
    }
}

fn needs_glue(request: &Request) -> bool {
    if request.context.iter().any(Term::has_glue) {
        return true;
    }
    match &request.judgment {
        Judgment::Has { term, ty } | Judgment::RestrictedHas { term, ty, .. } => {
            term.has_glue() || ty.has_glue()
        }
        Judgment::Equal { left, right, ty }
        | Judgment::RestrictedEqual {
            left, right, ty, ..
        } => left.has_glue() || right.has_glue() || ty.has_glue(),
        Judgment::Definition {
            definition,
            expansion,
        } => definition.arguments().into_iter().any(Term::has_glue) || expansion.has_glue(),
        _ => false,
    }
}

/// Generate fresh evidence, fix goals from the requests (not from inferred
/// answers), and accept only after the unchanged ground kernel replays it.
pub fn produce(requests: &[Request]) -> Result<Generated> {
    produce_selected(requests, None)
}

/// Select a fixed, audited fragment prefix, never caller-supplied rules.
/// Requests requiring a larger prefix are rejected before generation.
pub fn produce_with_profile(requests: &[Request], profile: Profile) -> Result<Generated> {
    produce_selected(requests, Some(profile))
}

fn produce_selected(requests: &[Request], selected: Option<Profile>) -> Result<Generated> {
    if requests.is_empty() || requests.len() > 128 {
        return Err("expected 1..128 cubical requests".into());
    }
    for request in requests {
        validate(request).map_err(|e| format!("{}: {e}", request.name))?;
    }
    let required = if requests.iter().any(needs_glue) {
        Profile::Glue
    } else if requests.iter().any(needs_equivalence) {
        Profile::Equivalence
    } else if requests.iter().any(needs_sigma) {
        Profile::Sigma
    } else if requests.iter().any(needs_composition) {
        Profile::Composition
    } else if requests.iter().any(needs_systems) {
        Profile::Systems
    } else if requests.iter().any(|r| {
        matches!(
            r.judgment,
            Judgment::Entails { .. } | Judgment::Local { .. }
        )
    }) {
        Profile::Faces
    } else {
        Profile::Path
    };
    let profile = selected.unwrap_or(required);
    if profile.fragments() < required.fragments() {
        return Err(format!(
            "selected profile {profile:?} does not include the required {required:?} fragment"
        ));
    }
    let theory = profile.theory();
    let mut p = Producer {
        profile,
        ..Producer::default()
    };
    let lowered = if profile >= Profile::Equivalence {
        Some(
            requests
                .iter()
                .map(|r| p.lower_request(r))
                .collect::<Result<Vec<_>>>()?,
        )
    } else {
        None
    };
    let requests = lowered.as_deref().unwrap_or(requests);
    let mut goals = String::new();
    let mut results = Vec::new();
    let mut names = std::collections::BTreeSet::new();
    for request in requests {
        if !names.insert(&request.name) {
            return Err(format!("duplicate goal name {}", request.name));
        }
        let d = request.dimensions;
        let g = &request.context;
        let prefix = [number(d), context(g)];
        let run = |p: &mut Producer| -> Result<(usize, Sexp)> {
            match &request.judgment {
                Judgment::Definition {
                    definition,
                    expansion,
                } => {
                    p.definition_arguments((d, g), definition)?;
                    p.request_universe(d, g, expansion)?;
                    let (actual, id) = p.expand_definition(definition)?;
                    if actual.quote() != expansion.quote() {
                        return Err("definition expansion does not match the requested term".into());
                    }
                    let args = definition
                        .arguments()
                        .into_iter()
                        .map(Term::quote)
                        .chain([expansion.quote()]);
                    return Ok((id, call(definition.predicate(), args)));
                }
                Judgment::Entails {
                    premise,
                    conclusion,
                } => {
                    p.request_ctx(d, g)?;
                    return Ok((
                        p.entails(d, premise, conclusion)?,
                        call("entails", [number(d), premise.quote(), conclusion.quote()]),
                    ));
                }
                Judgment::Local { face, left, right } => {
                    p.request_ctx(d, g)?;
                    return Ok((
                        p.local(d, face, left, right)?,
                        call(
                            "local",
                            [number(d), face.quote(), left.quote(), right.quote()],
                        ),
                    ));
                }
                Judgment::RestrictedHas { face, term, ty } => {
                    let id = p.restricted_check(d, g, face, term, ty)?;
                    return Ok((
                        id,
                        call(
                            "rhas",
                            [
                                number(d),
                                context(g),
                                face.quote(),
                                term.quote(),
                                ty.quote(),
                            ],
                        ),
                    ));
                }
                Judgment::RestrictedEqual {
                    face,
                    left,
                    right,
                    ty,
                } => {
                    let id = p.restricted_equal((d, g), face, left, right, ty)?;
                    return Ok((
                        id,
                        call(
                            "req",
                            [
                                number(d),
                                context(g),
                                face.quote(),
                                left.quote(),
                                right.quote(),
                                ty.quote(),
                            ],
                        ),
                    ));
                }
                _ => {}
            }
            let (id, pred, terms) = match &request.judgment {
                Judgment::Has { term, ty } => {
                    p.request_universe(d, g, ty)?;
                    (
                        p.request_check(d, g, term, ty)?,
                        "has",
                        vec![term.quote(), ty.quote()],
                    )
                }
                Judgment::Equal { left, right, ty } => {
                    p.request_universe(d, g, ty)?;
                    (
                        if matches!(
                            profile,
                            Profile::Composition
                                | Profile::Sigma
                                | Profile::Equivalence
                                | Profile::Glue
                                | Profile::Equality
                        ) {
                            let restricted =
                                p.restricted_equal((d, g), &Face::True, left, right, ty)?;
                            p.equality_step(
                                "req.export",
                                vec![restricted],
                                (d, g),
                                left,
                                right,
                                ty,
                            )?
                        } else {
                            p.equal(d, g, left, right, ty)?
                        },
                        "eq",
                        vec![left.quote(), right.quote(), ty.quote()],
                    )
                }
                _ => unreachable!("face requests handled above"),
            };
            Ok((id, call(pred, prefix.iter().cloned().chain(terms))))
        };
        let (id, goal) = run(&mut p).map_err(|e| format!("{}: {e}", request.name))?;
        let _ = writeln!(goals, "(goal {} {goal})", request.name);
        results.push((&request.name, id));
    }
    let mut proof = String::new();
    for (id, (rule, refs, judgment)) in p.steps.iter().enumerate() {
        let refs: Vec<_> = refs.iter().map(usize::to_string).collect();
        let _ = writeln!(proof, "(step {id} {rule} ({}) {judgment})", refs.join(" "));
    }
    for (name, id) in results {
        let _ = writeln!(proof, "(result {name} {id})");
    }
    let checked = crate::kernel::Theory::parse(&theory)?
        .check(&goals, &proof)
        .map_err(|e| format!("generated certificate rejected: {e}"))?;
    Ok(Generated {
        profile,
        theory,
        goals,
        proof,
        checked,
    })
}
