//! Untrusted producer for the scoped PathP experiment. No kernel changes.
use crate::cubical::engine::frontend::{E, Producer, lam};
use crate::cubical::engine::term::{Result, Sexp, atom, call};
use std::collections::BTreeMap;

#[path = "face_ops.rs"]
mod face_ops;

fn num(n: usize) -> Sexp {
    crate::cubical::engine::frontend::number(n)
}
pub fn v(n: usize) -> Sexp {
    call("v", [num(n)])
}
pub fn dim(n: usize) -> Sexp {
    call("dim", [num(n)])
}
pub fn u(n: usize) -> Sexp {
    call("u", [num(n)])
}
pub fn path(a: Sexp, b: Sexp, c: Sexp) -> Sexp {
    call("path", [a, b, c])
}
pub fn papp(p: Sexp, r: Sexp) -> Sexp {
    call("papp", [p, r])
}
pub fn cons(a: Sexp, g: Sexp) -> Sexp {
    call("cons", [a, g])
}

fn shape(t: &Sexp) -> Result<(&str, &[Sexp])> {
    match t {
        Sexp::Atom(s) => Ok((s, &[])),
        Sexp::List(xs) => Ok((xs.first().ok_or("empty expression")?.atom()?, &xs[1..])),
    }
}
fn natural(t: &Sexp) -> Result<usize> {
    match shape(t)? {
        ("z", []) => Ok(0),
        ("s", [n]) => Ok(natural(n)? + 1),
        _ => Err("expected unary natural".into()),
    }
}

#[derive(Clone, Debug)]
pub enum Op {
    Shift(usize),
    Subst(usize, Sexp),
    DShift(usize),
    DSubst(usize, Sexp),
}
impl Op {
    fn prefix(&self) -> &str {
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
    fn replacement(&self) -> Option<&Sexp> {
        match self {
            Self::Subst(_, r) | Self::DSubst(_, r) => Some(r),
            _ => None,
        }
    }
    fn dimension(&self) -> bool {
        matches!(self, Self::DShift(_) | Self::DSubst(..))
    }
}

type TransformKey = (u8, usize, usize, Option<usize>);
#[derive(Default)]
struct TransformMemo {
    terms: std::collections::HashMap<Sexp, usize>,
    values: Vec<Sexp>,
    operations: BTreeMap<TransformKey, (usize, usize)>,
}
impl TransformMemo {
    fn intern(&mut self, t: &Sexp) -> usize {
        if let Some(id) = self.terms.get(t) {
            return *id;
        }
        let id = self.values.len();
        self.terms.insert(t.clone(), id);
        self.values.push(t.clone());
        id
    }
}
#[derive(Default)]
pub struct PathProducer {
    pub p: Producer,
    inferred: BTreeMap<Sexp, (Sexp, usize)>,
    transformations: Option<TransformMemo>,
}

impl PathProducer {
    #[allow(dead_code)]
    pub fn memoize_transformations(&mut self) {
        self.transformations = Some(TransformMemo::default());
    }
    pub fn memoization_enabled(&self) -> bool {
        self.transformations.is_some()
    }
    fn fact(&mut self, rule: &str, refs: Vec<usize>, pred: &str, args: Vec<Sexp>) -> usize {
        self.p.emit(rule, refs, call(pred, args))
    }
    pub(crate) fn comparison(&mut self, m: usize, n: usize, strict: bool) -> Result<usize> {
        if (strict && m >= n) || (!strict && m > n) {
            return Err("false index comparison".into());
        }
        let pred = if strict { "lt" } else { "le" };
        let (suffix, refs) = if m == 0 {
            ("z", vec![])
        } else {
            ("s", vec![self.comparison(m - 1, n - 1, strict)?])
        };
        Ok(self.fact(
            &format!("{pred}.{suffix}"),
            refs,
            pred,
            vec![num(m), num(n)],
        ))
    }
    pub(crate) fn max(&mut self, m: usize, n: usize) -> usize {
        let (suffix, refs) = if m == 0 {
            ("z", vec![])
        } else if n == 0 {
            ("sz", vec![])
        } else {
            ("ss", vec![self.max(m - 1, n - 1)])
        };
        self.fact(
            &format!("max.{suffix}"),
            refs,
            "max",
            vec![num(m), num(n), num(m.max(n))],
        )
    }

    // Crossing each binder changes a different namespace. Every lift is certified.
    fn under(&mut self, op: &Op, dimension_binder: bool, refs: &mut Vec<usize>) -> Result<Op> {
        let k = op.cutoff();
        Ok(match (op, dimension_binder) {
            (Op::Shift(_), false) => Op::Shift(k + 1),
            (Op::Subst(_, r), false) => {
                let (r2, id) = self.transform(r, &Op::Shift(0))?;
                refs.push(id);
                Op::Subst(k + 1, r2)
            }
            (Op::Subst(_, r), true) => {
                let (r2, id) = self.transform(r, &Op::DShift(0))?;
                refs.push(id);
                Op::Subst(k, r2)
            }
            (Op::DShift(_), true) => Op::DShift(k + 1),
            (Op::DSubst(_, r), true) => {
                let (r2, id) = self.itransform(r, &Op::DShift(0))?;
                refs.push(id);
                Op::DSubst(k + 1, r2)
            }
            _ => op.clone(),
        })
    }

    pub fn transform(&mut self, t: &Sexp, op: &Op) -> Result<(Sexp, usize)> {
        let key = if let Some(memo) = &mut self.transformations {
            let input = memo.intern(t);
            let replacement = op.replacement().map(|r| memo.intern(r));
            let kind = match op {
                Op::Shift(_) => 0,
                Op::Subst(..) => 1,
                Op::DShift(_) => 2,
                Op::DSubst(..) => 3,
            };
            let key = (kind, input, op.cutoff(), replacement);
            if let Some((out, id)) = memo.operations.get(&key) {
                return Ok((memo.values[*out].clone(), *id));
            }
            Some(key)
        } else {
            None
        };
        let (head, args) = shape(t)?;
        let k = op.cutoff();
        let mut refs = Vec::new();
        let mut suffix = head.to_owned();
        let out = match (head, args) {
            ("u", [_]) | ("nat", []) | ("zero", []) => t.clone(),
            ("bool" | "btrue" | "bfalse", []) => t.clone(),
            ("bif", [p, tt, f, b]) => {
                let pop = self.under(op, false, &mut refs)?;
                let (p2, id) = self.transform(p, &pop)?;
                refs.push(id);
                let mut rest = Vec::new();
                for x in [tt, f, b] {
                    let (x2, id) = self.transform(x, op)?;
                    refs.push(id);
                    rest.push(x2);
                }
                let [t2, f2, b2]: [Sexp; 3] = rest.try_into().unwrap();
                call("bif", [p2, t2, f2, b2])
            }
            ("v", [n]) if op.dimension() => {
                let _ = n;
                t.clone()
            }
            ("v", [n]) => {
                let n = natural(n)?;
                if let Some(r) = op.replacement() {
                    if n == k {
                        suffix = "v.hit".into();
                        r.clone()
                    } else if n < k {
                        suffix = "v.lt".into();
                        refs.push(self.comparison(n, k, true)?);
                        t.clone()
                    } else {
                        suffix = "v.gt".into();
                        refs.push(self.comparison(k, n, true)?);
                        v(n - 1)
                    }
                } else if n < k {
                    suffix = "v.lt".into();
                    refs.push(self.comparison(n, k, true)?);
                    t.clone()
                } else {
                    suffix = "v.ge".into();
                    refs.push(self.comparison(k, n, false)?);
                    v(n + 1)
                }
            }
            ("pi" | "sigma", [a, b]) | ("app" | "pair" | "ann", [a, b]) => {
                let (a2, id) = self.transform(a, op)?;
                refs.push(id);
                let bop = if head == "pi" || head == "sigma" {
                    self.under(op, false, &mut refs)?
                } else {
                    op.clone()
                };
                let (b2, id) = self.transform(b, &bop)?;
                refs.push(id);
                call(head, [a2, b2])
            }
            ("lam", [body]) | ("plam", [body]) => {
                let bop = self.under(op, head == "plam", &mut refs)?;
                let (b2, id) = self.transform(body, &bop)?;
                refs.push(id);
                call(head, [b2])
            }
            ("fst" | "snd" | "unglue", [body]) => {
                let (out, id) = self.transform(body, op)?;
                refs.push(id);
                call(head, [out])
            }
            ("path", [a, b, c]) => {
                let aop = self.under(op, true, &mut refs)?;
                let (a2, id) = self.transform(a, &aop)?;
                refs.push(id);
                let (b2, id) = self.transform(b, op)?;
                refs.push(id);
                let (c2, id) = self.transform(c, op)?;
                refs.push(id);
                path(a2, b2, c2)
            }
            ("papp", [p, r]) => {
                let (p2, id) = self.transform(p, op)?;
                refs.push(id);
                let r2 = if op.dimension() {
                    let (r2, id) = self.itransform(r, op)?;
                    refs.push(id);
                    r2
                } else {
                    r.clone()
                };
                papp(p2, r2)
            }
            ("system", [s]) => {
                let (s2, id) = self.stransform(s, op)?;
                refs.push(id);
                call("system", [s2])
            }
            ("glue-type", [a, phi, t, e]) => {
                let (a2, id) = self.transform(a, op)?;
                refs.push(id);
                let phi2 = if op.dimension() {
                    let (phi2, id) = self.ftransform(phi, op)?;
                    refs.push(id);
                    phi2
                } else {
                    phi.clone()
                };
                let (t2, id) = self.transform(t, op)?;
                refs.push(id);
                let (e2, id) = self.transform(e, op)?;
                refs.push(id);
                call("glue-type", [a2, phi2, t2, e2])
            }
            ("glue", [g, t, a]) => {
                let (g2, id) = self.transform(g, op)?;
                refs.push(id);
                let (t2, id) = self.transform(t, op)?;
                refs.push(id);
                let (a2, id) = self.transform(a, op)?;
                refs.push(id);
                call("glue", [g2, t2, a2])
            }
            ("comp", [a, phi, tube, base]) => {
                let bop = self.under(op, true, &mut refs)?;
                let (a2, id) = self.transform(a, &bop)?;
                refs.push(id);
                let phi2 = if op.dimension() {
                    let (phi2, id) = self.ftransform(phi, op)?;
                    refs.push(id);
                    phi2
                } else {
                    phi.clone()
                };
                let (tube2, id) = self.transform(tube, &bop)?;
                refs.push(id);
                let (base2, id) = self.transform(base, op)?;
                refs.push(id);
                call("comp", [a2, phi2, tube2, base2])
            }
            _ => return Err(format!("unknown term shape {t}")),
        };
        let mut args = vec![t.clone(), num(k)];
        if let Some(r) = op.replacement() {
            args.push(r.clone());
        }
        args.push(out.clone());
        let id = self.fact(
            &format!("{}.{suffix}", op.prefix()),
            refs,
            op.prefix(),
            args,
        );
        if let (Some(memo), Some(key)) = (&mut self.transformations, key) {
            let output = memo.intern(&out);
            memo.operations.insert(key, (output, id));
        }
        Ok((out, id))
    }

    pub fn itransform(&mut self, t: &Sexp, op: &Op) -> Result<(Sexp, usize)> {
        if !op.dimension() {
            return Err("interval transformation needs dimension operation".into());
        }
        let prefix = if op.replacement().is_some() {
            "isubst"
        } else {
            "ishift"
        };
        let (head, args) = shape(t)?;
        let k = op.cutoff();
        let mut refs = Vec::new();
        let mut suffix = head.to_owned();
        let out = match (head, args) {
            ("i0", []) => {
                suffix = "0".into();
                t.clone()
            }
            ("i1", []) => {
                suffix = "1".into();
                t.clone()
            }
            ("dim", [n]) => {
                let n = natural(n)?;
                if let Some(r) = op.replacement() {
                    if n == k {
                        suffix = "dim.hit".into();
                        r.clone()
                    } else if n < k {
                        suffix = "dim.lt".into();
                        refs.push(self.comparison(n, k, true)?);
                        t.clone()
                    } else {
                        suffix = "dim.gt".into();
                        refs.push(self.comparison(k, n, true)?);
                        dim(n - 1)
                    }
                } else if n < k {
                    suffix = "dim.lt".into();
                    refs.push(self.comparison(n, k, true)?);
                    t.clone()
                } else {
                    suffix = "dim.ge".into();
                    refs.push(self.comparison(k, n, false)?);
                    dim(n + 1)
                }
            }
            ("neg", [r]) => {
                let (r2, id) = self.itransform(r, op)?;
                refs.push(id);
                call(head, [r2])
            }
            ("meet", [r, s]) | ("join", [r, s]) => {
                let (r2, id) = self.itransform(r, op)?;
                refs.push(id);
                let (s2, id) = self.itransform(s, op)?;
                refs.push(id);
                call(head, [r2, s2])
            }
            _ => return Err(format!("unknown interval shape {t}")),
        };
        let mut args = vec![t.clone(), num(k)];
        if let Some(r) = op.replacement() {
            args.push(r.clone());
        }
        args.push(out.clone());
        let id = self.fact(&format!("{prefix}.{suffix}"), refs, prefix, args);
        Ok((out, id))
    }

    pub fn dshiftctx(&mut self, g: &Sexp, k: usize) -> Result<(Sexp, usize)> {
        let key = if let Some(memo) = &mut self.transformations {
            let input = memo.intern(g);
            let key = (4, input, k, None);
            if let Some((out, id)) = memo.operations.get(&key) {
                return Ok((memo.values[*out].clone(), *id));
            }
            Some(key)
        } else {
            None
        };
        let (out, rule, refs) = match shape(g)? {
            ("nil", []) => (atom("nil"), "dshiftctx.nil", vec![]),
            ("cons", [a, tail]) => {
                let (tail2, tail_id) = self.dshiftctx(tail, k)?;
                let (a2, a_id) = self.transform(a, &Op::DShift(k))?;
                (cons(a2, tail2), "dshiftctx.cons", vec![tail_id, a_id])
            }
            _ => return Err("invalid context".into()),
        };
        let id = self.fact(
            rule,
            refs,
            "dshiftctx",
            vec![g.clone(), num(k), out.clone()],
        );
        if let (Some(memo), Some(key)) = (&mut self.transformations, key) {
            let output = memo.intern(&out);
            memo.operations.insert(key, (output, id));
        }
        Ok((out, id))
    }
    pub fn interval(&mut self, d: usize, r: &Sexp) -> Result<usize> {
        if self.memoization_enabled()
            && let Some(id) = self.p.known_judgment(&call("interval", [num(d), r.clone()]))
        {
            return Ok(id);
        }
        let (head, args) = shape(r)?;
        let (suffix, refs) = match (head, args) {
            ("i0", []) => ("0", vec![]),
            ("i1", []) => ("1", vec![]),
            ("dim", [n]) => ("dim", vec![self.comparison(natural(n)?, d, true)?]),
            ("neg", [r]) => ("neg", vec![self.interval(d, r)?]),
            ("meet", [r, s]) | ("join", [r, s]) => {
                (head, vec![self.interval(d, r)?, self.interval(d, s)?])
            }
            _ => return Err("invalid interval expression".into()),
        };
        Ok(self.fact(
            &format!("interval.{suffix}"),
            refs,
            "interval",
            vec![num(d), r.clone()],
        ))
    }
    fn level(a: &Sexp) -> Result<usize> {
        match shape(a)? {
            ("u", [n]) => natural(n),
            _ => Err(format!("expected universe: {a}")),
        }
    }
    fn ctx(&mut self, d: usize, g: &Sexp) -> Result<usize> {
        let (rule, refs) = match shape(g)? {
            ("nil", []) => ("ctx.nil", vec![]),
            ("cons", [a, tail]) => {
                let tail_id = self.ctx(d, tail)?;
                let (ty, a_id) = self.infer(d, tail, a)?;
                Self::level(&ty)?;
                ("ctx.cons", vec![tail_id, a_id])
            }
            _ => return Err("invalid context".into()),
        };
        Ok(self.fact(rule, refs, "ctx", vec![num(d), g.clone()]))
    }
    pub(crate) fn lookup(&mut self, g: &Sexp, n: usize) -> Result<(Sexp, usize)> {
        let ("cons", [a, tail]) = shape(g)? else {
            return Err("unbound term variable".into());
        };
        let (ty, rule, refs) = if n == 0 {
            let (a2, id) = self.transform(a, &Op::Shift(0))?;
            (a2, "lookup.z", vec![id])
        } else {
            let (a, id) = self.lookup(tail, n - 1)?;
            let (a2, shift) = self.transform(&a, &Op::Shift(0))?;
            (a2, "lookup.s", vec![id, shift])
        };
        let id = self.fact(rule, refs, "lookup", vec![g.clone(), num(n), ty.clone()]);
        Ok((ty, id))
    }
    pub fn infer(&mut self, d: usize, g: &Sexp, t: &Sexp) -> Result<(Sexp, usize)> {
        let key = call("infer", [num(d), g.clone(), t.clone()]);
        if let Some(result) = self.inferred.get(&key) {
            return Ok(result.clone());
        }
        let (ty, rule, refs) = match shape(t)? {
            ("u", [n]) => (u(natural(n)? + 1), "type.u", vec![self.ctx(d, g)?]),
            ("nat", []) => (u(0), "type.nat", vec![self.ctx(d, g)?]),
            ("zero", []) => (atom("nat"), "type.zero", vec![self.ctx(d, g)?]),
            ("v", [n]) => {
                let ctx = self.ctx(d, g)?;
                let (a, id) = self.lookup(g, natural(n)?)?;
                (a, "type.v", vec![ctx, id])
            }
            ("pi", [a, b]) => {
                let (ua, ai) = self.infer(d, g, a)?;
                let (ub, bi) = self.infer(d, &cons(a.clone(), g.clone()), b)?;
                let i = Self::level(&ua)?;
                let j = Self::level(&ub)?;
                (u(i.max(j)), "type.pi", vec![ai, bi, self.max(i, j)])
            }
            ("app", [f, a]) => {
                let (fty, fi) = self.infer(d, g, f)?;
                let ("pi", [domain, codomain]) = shape(&fty)? else {
                    return Err("expected Pi type".into());
                };
                let ai = self.check(d, g, a, domain)?;
                let (ty, si) = self.transform(codomain, &Op::Subst(0, a.clone()))?;
                (ty, "type.app", vec![fi, ai, si])
            }
            ("path", [a, b, c]) => {
                let ctx = self.ctx(d, g)?;
                let (g2, gi) = self.dshiftctx(g, 0)?;
                let (ua, ai) = self.infer(d + 1, &g2, a)?;
                Self::level(&ua)?;
                let (a0, s0) = self.transform(a, &Op::DSubst(0, atom("i0")))?;
                let (a1, s1) = self.transform(a, &Op::DSubst(0, atom("i1")))?;
                let bi = self.check(d, g, b, &a0)?;
                let ci = self.check(d, g, c, &a1)?;
                (ua, "type.path", vec![ctx, gi, ai, s0, s1, bi, ci])
            }
            ("plam", [body]) => {
                let ctx = self.ctx(d, g)?;
                let (g2, gi) = self.dshiftctx(g, 0)?;
                let (a, ti) = self.infer(d + 1, &g2, body)?;
                let (ua, ai) = self.infer(d + 1, &g2, &a)?;
                Self::level(&ua)?;
                let (a0, s0) = self.transform(&a, &Op::DSubst(0, atom("i0")))?;
                let (a1, s1) = self.transform(&a, &Op::DSubst(0, atom("i1")))?;
                let (t0, t0i) = self.transform(body, &Op::DSubst(0, atom("i0")))?;
                let (t1, t1i) = self.transform(body, &Op::DSubst(0, atom("i1")))?;
                let b0 = self.check(d, g, &t0, &a0)?;
                let b1 = self.check(d, g, &t1, &a1)?;
                (
                    path(a, t0, t1),
                    "type.plam",
                    vec![ctx, gi, ai, ti, s0, s1, t0i, t1i, b0, b1],
                )
            }
            ("papp", [p, r]) => {
                let (pty, pi) = self.infer(d, g, p)?;
                let ("path", [a, _, _]) = shape(&pty)? else {
                    return Err("expected PathP type".into());
                };
                let ri = self.interval(d, r)?;
                let (ar, si) = self.transform(a, &Op::DSubst(0, r.clone()))?;
                let (ua, ai) = self.infer(d, g, &ar)?;
                Self::level(&ua)?;
                (ar, "type.papp", vec![pi, ri, si, ai])
            }
            _ => return Err(format!("unsupported inference term {t}")),
        };
        let id = self.fact(
            rule,
            refs,
            "has",
            vec![num(d), g.clone(), t.clone(), ty.clone()],
        );
        self.inferred.insert(key, (ty.clone(), id));
        Ok((ty, id))
    }

    fn equality(
        &mut self,
        d: usize,
        g: &Sexp,
        equation: (&Sexp, &Sexp, &Sexp),
        rule: &str,
        refs: Vec<usize>,
    ) -> usize {
        let (a, b, ty) = equation;
        self.fact(
            rule,
            refs,
            "eq",
            vec![num(d), g.clone(), a.clone(), b.clone(), ty.clone()],
        )
    }
    pub fn endpoint(
        &mut self,
        d: usize,
        g: &Sexp,
        p: &Sexp,
        one: bool,
    ) -> Result<(Sexp, Sexp, usize)> {
        let (pty, pi) = self.infer(d, g, p)?;
        let ("path", [a, b, c]) = shape(&pty)? else {
            return Err("endpoint requires PathP".into());
        };
        let r = atom(if one { "i1" } else { "i0" });
        let out = if one { c } else { b };
        let (ar, si) = self.transform(a, &Op::DSubst(0, r.clone()))?;
        let oi = self.check(d, g, out, &ar)?;
        let id = self.equality(
            d,
            g,
            (&papp(p.clone(), r), out, &ar),
            if one { "eq.p1" } else { "eq.p0" },
            vec![pi, si, oi],
        );
        Ok((out.clone(), ar, id))
    }
    fn reduce(&mut self, d: usize, g: &Sexp, t: &Sexp) -> Result<(Sexp, Sexp, usize)> {
        if let ("papp", [p, r]) = shape(t)?
            && (*r == atom("i0") || *r == atom("i1"))
        {
            return self.endpoint(d, g, p, *r == atom("i1"));
        }
        let (ty, id) = self.infer(d, g, t)?;
        let eq = self.equality(d, g, (t, t, &ty), "eq.refl", vec![id]);
        Ok((t.clone(), ty, eq))
    }
    pub fn check(&mut self, d: usize, g: &Sexp, t: &Sexp, expected: &Sexp) -> Result<usize> {
        let (actual, ti) = self.infer(d, g, t)?;
        if actual == *expected {
            return Ok(ti);
        }
        let (a, ua, ai) = self.reduce(d, g, &actual)?;
        let (b, ub, bi) = self.reduce(d, g, expected)?;
        if a != b || ua != ub {
            return Err(format!(
                "conversion search failed: {actual} versus {expected}"
            ));
        }
        let sym = self.equality(d, g, (&b, expected, &ub), "eq.sym", vec![bi]);
        let eq = self.equality(d, g, (&actual, expected, &ua), "eq.trans", vec![ai, sym]);
        self.convert(d, g, t, expected, ti, eq)
    }
    fn convert(
        &mut self,
        d: usize,
        g: &Sexp,
        t: &Sexp,
        expected: &Sexp,
        ti: usize,
        eq: usize,
    ) -> Result<usize> {
        let (ue, ei) = self.infer(d, g, expected)?;
        Self::level(&ue)?;
        Ok(self.fact(
            "type.conv",
            vec![ti, eq, ei],
            "has",
            vec![num(d), g.clone(), t.clone(), expected.clone()],
        ))
    }
    pub fn beta(&mut self, d: usize, g: &Sexp, body: &Sexp, r: &Sexp) -> Result<usize> {
        let abstraction = call("plam", [body.clone()]);
        let (pty, pi) = self.infer(d, g, &abstraction)?;
        let ("path", [a, _, _]) = shape(&pty)? else {
            return Err("expected PathP".into());
        };
        let ri = self.interval(d, r)?;
        let (ar, si) = self.transform(a, &Op::DSubst(0, r.clone()))?;
        let (tr, ti) = self.transform(body, &Op::DSubst(0, r.clone()))?;
        let typed = self.check(d, g, &tr, &ar)?;
        Ok(self.equality(
            d,
            g,
            (&papp(abstraction, r.clone()), &tr, &ar),
            "eq.pbeta",
            vec![pi, ri, si, ti, typed],
        ))
    }
    fn pdim(
        &mut self,
        d: usize,
        g: &Sexp,
        p: &Sexp,
        r: &Sexp,
        s: &Sexp,
        ieq: usize,
    ) -> Result<(Sexp, usize)> {
        let (pty, pi) = self.infer(d, g, p)?;
        let ("path", [a, _, _]) = shape(&pty)? else {
            return Err("expected PathP".into());
        };
        let ri = self.interval(d, r)?;
        let si = self.interval(d, s)?;
        let (ar, ari) = self.transform(a, &Op::DSubst(0, r.clone()))?;
        let (as_, asi) = self.transform(a, &Op::DSubst(0, s.clone()))?;
        if ar != as_ {
            return Err("pdim requires identical substituted family types".into());
        }
        let (_, ai) = self.infer(d, g, &ar)?;
        let id = self.equality(
            d,
            g,
            (
                &papp(p.clone(), r.clone()),
                &papp(p.clone(), s.clone()),
                &ar,
            ),
            "eq.pdim",
            vec![pi, ri, si, ieq, ari, asi, ai],
        );
        Ok((ar, id))
    }
    fn lift_plain_identity(&mut self) -> Result<usize> {
        let mut old = Producer::default();
        let (_, root) = old.infer(&[], &lam(E::U(0), lam(E::V(0), E::V(0))))?;
        let mut ids = Vec::new();
        for (rule, refs, j) in old.steps {
            let mut xs = j.list()?.to_vec();
            if ["ctx", "has", "eq"].contains(&xs[0].atom()?) {
                xs.insert(1, num(0));
            }
            ids.push(self.p.emit(
                &rule,
                refs.iter().map(|n| ids[*n]).collect(),
                crate::cubical::engine::term::list(xs),
            ));
        }
        Ok(ids[root])
    }
}

pub fn path_demo() -> Result<PathProducer> {
    let mut q = PathProducer::default();
    let nil = atom("nil");
    let nat = atom("nat");
    let zero = atom("zero");
    let id = q.lift_plain_identity()?;
    q.p.result("dependent-id", id);
    let ty = path(nat.clone(), zero.clone(), zero.clone());
    let (_, id) = q.infer(0, &nil, &ty)?;
    q.p.result("path-formation", id);
    let refl = call("plam", [zero.clone()]);
    let (_, id) = q.infer(0, &nil, &refl)?;
    q.p.result("path-reflexivity", id);
    let id = q.beta(1, &nil, &zero, &dim(0))?;
    q.p.result("path-beta", id);
    // x:Nat, p:Path Nat zero x, so the two endpoints are distinct syntax.
    let g = cons(
        path(nat.clone(), zero.clone(), v(0)),
        cons(nat.clone(), nil.clone()),
    );
    let (_, _, id) = q.endpoint(0, &g, &v(0), false)?;
    q.p.result("endpoint-zero", id);
    let (_, _, id) = q.endpoint(0, &g, &v(0), true)?;
    q.p.result("endpoint-one", id);
    let reverse = call("plam", [papp(v(0), call("neg", [dim(0)]))]);
    let (raw, ri) = q.infer(0, &g, &reverse)?;
    let desired = path(nat.clone(), v(1), zero.clone());
    let mut boundary_proofs = Vec::new();
    for one in [false, true] {
        let from = atom(if one { "i1" } else { "i0" });
        let to = atom(if one { "i0" } else { "i1" });
        let neg = call("neg", [from]);
        let ieq = q.fact(
            if one { "i.neg-one" } else { "i.neg-zero" },
            vec![],
            "ieq",
            vec![neg.clone(), to.clone()],
        );
        let (a, cong) = q.pdim(0, &g, &v(0), &neg, &to, ieq)?;
        let (out, _, endpoint) = q.endpoint(0, &g, &v(0), !one)?;
        boundary_proofs.push(q.equality(
            0,
            &g,
            (&papp(v(0), neg), &out, &a),
            "eq.trans",
            vec![cong, endpoint],
        ));
    }
    let (_, raw_i) = q.infer(0, &g, &raw)?;
    let (_, desired_i) = q.infer(0, &g, &desired)?;
    let ("path", [family, _, _]) = shape(&raw)? else {
        unreachable!()
    };
    let (_, a0) = q.transform(family, &Op::DSubst(0, atom("i0")))?;
    let (_, a1) = q.transform(family, &Op::DSubst(0, atom("i1")))?;
    let eq = q.equality(
        0,
        &g,
        (&raw, &desired, &u(0)),
        "eq.path",
        vec![
            raw_i,
            desired_i,
            a0,
            a1,
            boundary_proofs[0],
            boundary_proofs[1],
        ],
    );
    let id = q.convert(0, &g, &reverse, &desired, ri, eq)?;
    q.p.result("path-reversal", id);
    let (_, id) = q.transform(&call("plam", [v(0)]), &Op::Subst(0, papp(v(1), dim(0))))?;
    q.p.result("term-subst-crosses-dimension", id);
    let (_, id) = q.transform(&call("plam", [papp(v(0), dim(1))]), &Op::DSubst(0, dim(0)))?;
    q.p.result("dimension-capture-avoidance", id);
    // P : Path U0 Nat Nat. A(i) = P i is genuinely dimension-dependent syntax.
    let pg = cons(path(u(0), nat.clone(), nat.clone()), nil);
    let dependent = path(papp(v(0), dim(0)), zero.clone(), zero.clone());
    let (_, id) = q.infer(0, &pg, &dependent)?;
    q.p.result("dependent-path-formation", id);
    let qg = cons(dependent, pg);
    let (_, id) = q.infer(1, &qg, &papp(v(0), dim(0)))?;
    q.p.result("dependent-path-application", id);
    let (_, _, id) = q.endpoint(0, &qg, &v(0), false)?;
    q.p.result("dependent-endpoint", id);
    // In ambient dimension i, x : P i. Introducing j must change P i to P (dim 1).
    let ambient = cons(
        papp(v(0), dim(0)),
        cons(path(u(0), nat.clone(), nat), atom("nil")),
    );
    let (_, id) = q.infer(1, &ambient, &call("plam", [v(0)]))?;
    q.p.result("dimension-dependent-context", id);
    let id = q.beta(1, &ambient, &v(0), &dim(0))?;
    q.p.result("beta-in-dimension-dependent-context", id);
    Ok(q)
}
