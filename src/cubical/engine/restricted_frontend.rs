//! Untrusted deep-syntax restricted typing, systems, and composition producer.
//! No Agda invocation, semantic univalence lemmas, or cubical kernel extensions.
use super::FUEL_TYPES;
use crate::cubical::engine::face_frontend::{Face, FaceProducer};
use crate::cubical::engine::frontend::number as num;
use crate::cubical::engine::path_frontend::{Op, cons, papp, path, u, v};
use crate::cubical::engine::term::{Result, Sexp, atom, call};
use std::collections::{BTreeMap, BTreeSet};

#[path = "computation_frontend.rs"]
#[allow(dead_code)]
mod computation_frontend;

#[path = "equivalence_ops.rs"]
#[allow(dead_code)]
mod equivalence_ops;

#[path = "equality_frontend.rs"]
#[allow(dead_code)]
mod equality_frontend;

#[path = "circle_frontend.rs"]
#[allow(dead_code)]
mod circle_frontend;

#[path = "data_frontend.rs"]
#[allow(dead_code)]
mod data_frontend;

#[path = "eliminator_frontend.rs"]
#[allow(dead_code)]
mod eliminator_frontend;

fn shape(t: &Sexp) -> Result<(&str, &[Sexp])> {
    match t {
        Sexp::Atom(a) => Ok((a, &[])),
        Sexp::List(xs) if !xs.is_empty() => Ok((xs[0].atom()?, &xs[1..])),
        _ => Err("empty expression".into()),
    }
}
fn natural(t: &Sexp) -> Result<usize> {
    match shape(t)? {
        ("z", []) => Ok(0),
        ("s", [n]) => Ok(natural(n)? + 1),
        _ => Err("invalid natural".into()),
    }
}
fn level(t: &Sexp) -> Result<usize> {
    match shape(t)? {
        ("u", [n]) => natural(n),
        _ => Err(format!("expected universe, got {t}")),
    }
}

#[derive(Default)]
pub struct RestrictedProducer {
    pub f: FaceProducer,
    inferred: BTreeMap<Sexp, (Sexp, usize)>,
    checked: BTreeMap<Sexp, usize>,
    equalities: BTreeMap<Sexp, usize>,
    equality_active: BTreeSet<Sexp>,
    restriction_hints: Option<BTreeMap<Sexp, Vec<(Face, Sexp)>>>,
    closed_annotation_reuse: bool,
    type_directed_composition: bool,
    certified_check_reuse: bool,
    typed_beta_reuse: bool,
    strengthening: bool,
    reduct_types: bool,
    /// With `keep_reduct_types`: where each term that needs an annotation was
    /// checked, by term, as (d, Γ, type). A failed inference of the same term
    /// in an extension of such a context retries with the transported type.
    checked_forms: BTreeMap<Sexp, Vec<(usize, Sexp, Sexp)>>,
}

/// Whether ordinary variable `k` occurs free in `t`.
fn mentions(t: &Sexp, k: usize) -> bool {
    match shape(t) {
        Ok(("v", [n])) => natural(n).is_ok_and(|n| n == k),
        Ok(("pi" | "sigma", [a, b])) => mentions(a, k) || mentions(b, k + 1),
        Ok(("lam", [b])) => mentions(b, k + 1),
        _ => match t {
            Sexp::List(xs) => xs.iter().skip(1).any(|x| mentions(x, k)),
            Sexp::Atom(_) => false,
        },
    }
}
impl RestrictedProducer {
    // Reuse only already certified typings on provably weaker restrictions.
    // The new local judgment is always emitted using rhas.weaken.
    pub fn reuse_restricted_typings(&mut self) {
        self.restriction_hints = Some(BTreeMap::new());
    }
    pub fn reuse_beta_typing(&mut self) {
        self.typed_beta_reuse = true;
    }
    pub fn reuse_certified_checks(&mut self) {
        self.certified_check_reuse = true;
    }
    pub fn enable_composition_computation(&mut self) {
        self.type_directed_composition = true;
    }
    pub fn reuse_closed_annotations(&mut self) {
        self.closed_annotation_reuse = true;
    }
    // Type a compound term that does not mention the newest ordinary
    // variable in the shorter context, then lift it with rhas.shift. Each
    // such typing is derived once and reused at every deeper binder.
    pub fn strengthen_typings(&mut self) {
        self.strengthening = true;
    }
    // Typed reduction. Reducts that need an annotation (systems, lambdas,
    // pairs, path abstractions) stay annotated with the type they were
    // reduced at (req.ann); β and Σ-β then compute through the annotation,
    // with the bare redex typed from it. Equality search reduces at the
    // known type when a term cannot be inferred, and a lambda or pair checked
    // in one context can be recalled under further binders. Earlier
    // producers do not use this mode, so their certificates are unchanged.
    pub fn keep_reduct_types(&mut self) {
        self.reduct_types = true;
    }
    /// The context's head and tail when `t` (and `a`, if given) can be typed
    /// without its newest variable; `t` is then lowered past it.
    fn strengthenable(&self, g: &Sexp, t: &Sexp, a: Option<&Sexp>) -> Option<(Sexp, Sexp)> {
        if !self.strengthening || matches!(shape(t), Ok(("v" | "u" | "nat" | "zero", _))) {
            return None;
        }
        let ("cons", [b, rest]) = shape(g).ok()? else {
            return None;
        };
        (!mentions(t, 0) && !a.is_some_and(|a| mentions(a, 0))).then(|| (b.clone(), rest.clone()))
    }
    /// Lift `rhas d rest φ t0 a0` (id0) to `rhas d (cons b rest) φ ↑t0 ↑a0`.
    #[allow(clippy::too_many_arguments)] // Context split, judgment, and its proof.
    fn lift(
        &mut self,
        d: usize,
        b: &Sexp,
        rest: &Sexp,
        phi: &Face,
        t0: &Sexp,
        a0: &Sexp,
        id0: usize,
    ) -> Result<(Sexp, Sexp, usize)> {
        let (ub, bi) = self.infer(d, rest, phi, b)?;
        level(&ub)?;
        let (t, ti) = self.f.path.transform(t0, &Op::Shift(0))?;
        let (a, ai) = self.f.path.transform(a0, &Op::Shift(0))?;
        let g = cons(b.clone(), rest.clone());
        let id = self.has(d, &g, phi, &t, &a, "rhas.shift", vec![id0, bi, ti, ai]);
        self.remember(d, &g, phi, &t, &a, id);
        Ok((t, a, id))
    }
    fn lower(&mut self, t: &Sexp) -> Result<Sexp> {
        Ok(self.f.path.transform(t, &Op::Subst(0, atom("zero")))?.0)
    }
    fn weaken_closed_annotation(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        a: &Sexp,
    ) -> Result<usize> {
        let mut ctx = atom("nil");
        let (mut universe, mut type_id) = self.infer(d, &ctx, phi, a)?;
        level(&universe)?;
        let mut term_id = self.check(d, &ctx, phi, t, a)?;
        let (mut value, mut ty) = (t.clone(), a.clone());
        let mut domains = Vec::new();
        let mut tail = g;
        while let ("cons", [dom, rest]) = shape(tail)? {
            domains.push(dom.clone());
            tail = rest;
        }
        if *tail != atom("nil") {
            return Err("invalid weakening target context".into());
        }
        for dom in domains.into_iter().rev() {
            let (ud, di) = self.infer(d, &ctx, phi, &dom)?;
            level(&ud)?;
            let (value2, vi) = self.f.path.transform(&value, &Op::Shift(0))?;
            let (ty2, ai) = self.f.path.transform(&ty, &Op::Shift(0))?;
            let (u2, ui) = self.f.path.transform(&universe, &Op::Shift(0))?;
            ctx = cons(dom, ctx);
            term_id = self.has(
                d,
                &ctx,
                phi,
                &value2,
                &ty2,
                "rhas.shift",
                vec![term_id, di, vi, ai],
            );
            type_id = self.has(
                d,
                &ctx,
                phi,
                &ty2,
                &u2,
                "rhas.shift",
                vec![type_id, di, ai, ui],
            );
            self.remember(d, &ctx, phi, &value2, &ty2, term_id);
            self.remember(d, &ctx, phi, &ty2, &u2, type_id);
            value = value2;
            ty = ty2;
            universe = u2;
        }
        if value != *t || ty != *a {
            return Err("annotation was not closed in ordinary variables".into());
        }
        Ok(term_id)
    }
    fn emit(&mut self, rule: &str, refs: Vec<usize>, j: Sexp) -> usize {
        self.f.path.p.emit(rule, refs, j)
    }
    #[allow(clippy::too_many_arguments)] // Mirrors the explicit Horn judgment and rule evidence.
    fn has(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        a: &Sexp,
        rule: &str,
        refs: Vec<usize>,
    ) -> usize {
        self.emit(
            rule,
            refs,
            call(
                "rhas",
                [num(d), g.clone(), phi.quote(), t.clone(), a.clone()],
            ),
        )
    }
    #[allow(clippy::too_many_arguments)] // Mirrors the explicit Horn judgment and rule evidence.
    fn eq(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        s: &Sexp,
        a: &Sexp,
        rule: &str,
        refs: Vec<usize>,
    ) -> usize {
        self.emit(
            rule,
            refs,
            call(
                "req",
                [
                    num(d),
                    g.clone(),
                    phi.quote(),
                    t.clone(),
                    s.clone(),
                    a.clone(),
                ],
            ),
        )
    }
    pub fn ctx(&mut self, d: usize, g: &Sexp, phi: &Face) -> Result<usize> {
        if self.f.path.memoization_enabled()
            && let Some(id) = self
                .f
                .path
                .p
                .known_judgment(&call("rctx", [num(d), g.clone(), phi.quote()]))
        {
            return Ok(id);
        }
        let normal = phi.normal();
        if normal != *phi {
            let entails = self.f.entails(d, phi, &normal)?;
            let ctx = self.ctx(d, g, &normal)?;
            return Ok(self.emit(
                "rctx.weaken",
                vec![entails, ctx],
                call("rctx", [num(d), g.clone(), phi.quote()]),
            ));
        }
        let (rule, refs) = match shape(g)? {
            ("nil", []) => ("rctx.nil", vec![self.f.face(d, phi)?]),
            ("cons", [a, tail]) => {
                let tail_id = self.ctx(d, tail, phi)?;
                let (ty, id) = self.infer(d, tail, phi, a)?;
                level(&ty)?;
                ("rctx.cons", vec![tail_id, id])
            }
            _ => return Err("invalid context".into()),
        };
        Ok(self.emit(rule, refs, call("rctx", [num(d), g.clone(), phi.quote()])))
    }
    fn length(&mut self, g: &Sexp) -> Result<(usize, usize)> {
        if self.f.path.memoization_enabled() {
            let mut tail = g;
            let mut n = 0;
            while let ("cons", [_, rest]) = shape(tail)? {
                n += 1;
                tail = rest;
            }
            if *tail != atom("nil") {
                return Err("invalid context".into());
            }
            if let Some(id) = self
                .f
                .path
                .p
                .known_judgment(&call("length", [g.clone(), num(n)]))
            {
                return Ok((n, id));
            }
        }
        let (n, rule, refs) = match shape(g)? {
            ("nil", []) => (0, "length.nil", vec![]),
            ("cons", [_, tail]) => {
                let (n, id) = self.length(tail)?;
                (n + 1, "length.cons", vec![id])
            }
            _ => return Err("invalid context".into()),
        };
        let id = self.emit(rule, refs, call("length", [g.clone(), num(n)]));
        Ok((n, id))
    }
    pub fn scope(&mut self, d: usize, n: usize, t: &Sexp) -> Result<usize> {
        if self.f.path.memoization_enabled()
            && let Some(id) = self
                .f
                .path
                .p
                .known_judgment(&call("scoped", [num(d), num(n), t.clone()]))
        {
            return Ok(id);
        }
        let (head, args) = shape(t)?;
        let refs = match (head, args) {
            ("u", [_]) | ("nat" | "zero", []) => vec![],
            ("bool" | "btrue" | "bfalse", []) => vec![],
            ("s1" | "base", []) => vec![],
            ("loop", [r]) => vec![self.f.path.interval(d, r)?],
            ("s1rec", xs) if xs.len() == 4 => {
                let mut refs = Vec::new();
                for x in xs {
                    refs.push(self.scope(d, n, x)?);
                }
                refs
            }
            ("suc", [x]) => vec![self.scope(d, n, x)?],
            ("bif" | "natrec", [p, tt, f, b]) => vec![
                self.scope(d, n + 1, p)?,
                self.scope(d, n, tt)?,
                self.scope(d, n, f)?,
                self.scope(d, n, b)?,
            ],
            ("v", [k]) => vec![self.f.path.comparison(natural(k)?, n, true)?],
            ("pi" | "sigma", [a, b]) => vec![self.scope(d, n, a)?, self.scope(d, n + 1, b)?],
            ("lam", [t]) => vec![self.scope(d, n + 1, t)?],
            ("app" | "pair" | "ann", [f, t]) => vec![self.scope(d, n, f)?, self.scope(d, n, t)?],
            ("fst" | "snd" | "unglue", [t]) => vec![self.scope(d, n, t)?],
            ("glue-type", [a, phi, t, e]) => vec![
                self.scope(d, n, a)?,
                self.f.face(d, &Face::parse(phi)?)?,
                self.scope(d, n, t)?,
                self.scope(d, n, e)?,
            ],
            ("glue", [g, t, a]) => vec![
                self.scope(d, n, g)?,
                self.scope(d, n, t)?,
                self.scope(d, n, a)?,
            ],
            ("path", [a, b, c]) => vec![
                self.scope(d + 1, n, a)?,
                self.scope(d, n, b)?,
                self.scope(d, n, c)?,
            ],
            ("plam", [t]) => vec![self.scope(d + 1, n, t)?],
            ("papp", [p, r]) => vec![self.scope(d, n, p)?, self.f.path.interval(d, r)?],
            ("system", [s]) => vec![self.sscope(d, n, s)?],
            ("comp", [a, phi, tube, base]) => vec![
                self.scope(d + 1, n, a)?,
                self.f.face(d, &Face::parse(phi)?)?,
                self.scope(d + 1, n, tube)?,
                self.scope(d, n, base)?,
            ],
            (h, xs) if crate::cubical::engine::data::is_declared(h) => {
                let motive = crate::cubical::engine::data::motive_index(h);
                let mut refs = Vec::new();
                for (i, x) in xs.iter().enumerate() {
                    let depth = if Some(i) == motive { n + 1 } else { n };
                    refs.push(self.scope(d, depth, x)?);
                }
                refs
            }
            _ => return Err(format!("unsupported syntax in scope: {t}")),
        };
        Ok(self.emit(
            &format!("scope.{head}"),
            refs,
            call("scoped", [num(d), num(n), t.clone()]),
        ))
    }
    fn sscope(&mut self, d: usize, n: usize, s: &Sexp) -> Result<usize> {
        let (suffix, refs) = match shape(s)? {
            ("snil", []) => ("nil", vec![]),
            ("side", [phi, t, rest]) => (
                "side",
                vec![
                    self.f.face(d, &Face::parse(phi)?)?,
                    self.scope(d, n, t)?,
                    self.sscope(d, n, rest)?,
                ],
            ),
            _ => return Err("invalid system syntax".into()),
        };
        Ok(self.emit(
            &format!("sscope.{suffix}"),
            refs,
            call("sscoped", [num(d), num(n), s.clone()]),
        ))
    }
    pub fn infer(&mut self, d: usize, g: &Sexp, phi: &Face, t: &Sexp) -> Result<(Sexp, usize)> {
        let key = call("rhas-key", [num(d), g.clone(), phi.quote(), t.clone()]);
        if let Some(result) = self.inferred.get(&key) {
            return Ok(result.clone());
        }
        if let Some(hints) = &self.restriction_hints {
            let hint_key = call("typing-hints", [num(d), g.clone(), t.clone()]);
            let candidates = hints.get(&hint_key).cloned().unwrap_or_default();
            let normal = phi.normal();
            for (source, source_key) in candidates {
                if source == *phi || phi.clone().and(source.clone()).normal() != normal {
                    continue;
                }
                let Some((ty, source_id)) = self.inferred.get(&source_key).cloned() else {
                    continue;
                };
                if let Ok(entails) = self.f.entails(d, phi, &source) {
                    let id = self.has(d, g, phi, t, &ty, "rhas.weaken", vec![entails, source_id]);
                    self.remember(d, g, phi, t, &ty, id);
                    return Ok((ty, id));
                }
            }
        }
        let normal = phi.normal();
        if normal != *phi {
            let entails = self.f.entails(d, phi, &normal)?;
            let (ty, id) = self.infer(d, g, &normal, t)?;
            let id = self.has(d, g, phi, t, &ty, "rhas.weaken", vec![entails, id]);
            self.remember(d, g, phi, t, &ty, id);
            return Ok((ty, id));
        }
        // A failed attempt in the shorter context falls back to the ordinary
        // search, which may try other candidates.
        if let Some((b, rest)) = self.strengthenable(g, t, None)
            && let Ok(t0) = self.lower(t)
            && let Ok((a0, id0)) = self.infer(d, &rest, phi, &t0)
        {
            let (t2, a, id) = self.lift(d, &b, &rest, phi, &t0, &a0, id0)?;
            if t2 == *t {
                return Ok((a, id));
            }
        }
        let (ty, rule, refs) = match shape(t)? {
            ("ann", [t, a]) => {
                let ti = if self.closed_annotation_reuse
                    && *g != atom("nil")
                    && self.scope(d, 0, t).is_ok()
                    && self.scope(d, 0, a).is_ok()
                {
                    Some(self.weaken_closed_annotation(d, g, phi, t, a)?)
                } else {
                    None
                };
                let (ua, ai) = self.infer(d, g, phi, a)?;
                level(&ua)?;
                let ti = if let Some(ti) = ti {
                    ti
                } else {
                    self.check(d, g, phi, t, a)?
                };
                (a.clone(), "rhas.ann", vec![ai, ti])
            }
            ("u", [l]) => (u(natural(l)? + 1), "rhas.u", vec![self.ctx(d, g, phi)?]),
            ("nat", []) => (u(0), "rhas.nat", vec![self.ctx(d, g, phi)?]),
            ("zero", []) => (atom("nat"), "rhas.zero", vec![self.ctx(d, g, phi)?]),
            ("bool", []) => (u(0), "rhas.bool", vec![self.ctx(d, g, phi)?]),
            (head @ ("btrue" | "bfalse"), []) => (
                atom("bool"),
                if head == "btrue" {
                    "rhas.btrue"
                } else {
                    "rhas.bfalse"
                },
                vec![self.ctx(d, g, phi)?],
            ),
            ("suc", [x]) => {
                let xi = self.check(d, g, phi, x, &atom("nat"))?;
                (atom("nat"), "rhas.suc", vec![xi])
            }
            ("natrec", [p, z, f, m]) => {
                let nat = atom("nat");
                let gn = cons(nat.clone(), g.clone());
                let (up, pi) = self.infer(d, &gn, phi, p)?;
                let l = level(&up)?;
                let (pz, szi) = self.f.path.transform(p, &Op::Subst(0, atom("zero")))?;
                let zi = self.check(d, g, phi, z, &pz)?;
                let (p1, sh1) = self.f.path.transform(p, &Op::Shift(1))?;
                let (p2, sh2) = self.f.path.transform(&p1, &Op::Shift(1))?;
                let (psk, ssk) = self
                    .f
                    .path
                    .transform(&p2, &Op::Subst(0, call("suc", [v(1)])))?;
                let step = call("pi", [nat.clone(), call("pi", [p.clone(), psk])]);
                let fi = self.check(d, g, phi, f, &step)?;
                let mi = self.check(d, g, phi, m, &nat)?;
                let (pm, smi) = self.f.path.transform(p, &Op::Subst(0, m.clone()))?;
                let ui = self.check(d, g, phi, &pm, &u(l))?;
                (
                    pm,
                    "rhas.natrec",
                    vec![pi, szi, zi, sh1, sh2, ssk, fi, mi, smi, ui],
                )
            }
            ("bif", [p, tt, f, b]) => {
                let gb = cons(atom("bool"), g.clone());
                let (up, pi) = self.infer(d, &gb, phi, p)?;
                let l = level(&up)?;
                let (pt, sti) = self.f.path.transform(p, &Op::Subst(0, atom("btrue")))?;
                let ti = self.check(d, g, phi, tt, &pt)?;
                let (pf, sfi) = self.f.path.transform(p, &Op::Subst(0, atom("bfalse")))?;
                let fi = self.check(d, g, phi, f, &pf)?;
                let bi = self.check(d, g, phi, b, &atom("bool"))?;
                let (pb, sbi) = self.f.path.transform(p, &Op::Subst(0, b.clone()))?;
                let ui = self.check(d, g, phi, &pb, &u(l))?;
                (pb, "rhas.bif", vec![pi, sti, ti, sfi, fi, bi, sbi, ui])
            }
            ("v", [n]) => {
                let c = self.ctx(d, g, phi)?;
                let (ty, id) = self.f.path.lookup(g, natural(n)?)?;
                (ty, "rhas.v", vec![c, id])
            }
            ("system", [s]) => {
                // A candidate type comes from an inhabited branch. The whole
                // system is then checked at that candidate, including coverage
                // and every overlap; branch inference is not an oracle rule.
                let mut rest = s;
                let mut first = None;
                let candidate = loop {
                    let ("side", [f, value, tail]) = shape(rest)? else {
                        let Some((restricted, value)) = first else {
                            return Err(format!("cannot infer a type for an empty system: {t}"));
                        };
                        // Under false, inference still needs a type candidate;
                        // the checked false rule enforces scope and formation.
                        break self.infer(d, g, &restricted, value)?.0;
                    };
                    let restricted = phi.clone().and(Face::parse(f)?);
                    if first.is_none() {
                        first = Some((restricted.clone(), value));
                    }
                    if self.f.entails(d, &restricted, &Face::False).is_err() {
                        break self.infer(d, g, &restricted, value)?.0;
                    }
                    rest = tail;
                };
                let id = self.check(d, g, phi, t, &candidate)?;
                self.remember(d, g, phi, t, &candidate, id);
                return Ok((candidate, id));
            }
            (head @ ("pi" | "sigma"), [a, b]) => {
                let (ua, ai) = self.infer(d, g, phi, a)?;
                let (ub, bi) = self.infer(d, &cons(a.clone(), g.clone()), phi, b)?;
                let (i, j) = (level(&ua)?, level(&ub)?);
                (
                    u(i.max(j)),
                    if head == "pi" {
                        "rhas.pi"
                    } else {
                        "rhas.sigma"
                    },
                    vec![ai, bi, self.f.path.max(i, j)],
                )
            }
            ("app", [f, a]) => {
                // Recover an erased lambda domain from this argument. The
                // candidate is still checked by ordinary typing rules.
                let recover = |p: &mut Self, body: &Sexp| -> Result<(Sexp, usize)> {
                    let (at, _) = p.infer(d, g, phi, a)?;
                    let (bt, _) = p.infer(d, &cons(at.clone(), g.clone()), phi, body)?;
                    let ft = call("pi", [at, bt]);
                    let fi = p.check(d, g, phi, f, &ft)?;
                    Ok((ft, fi))
                };
                let (mut fty, mut fi) = if let Ok(typed) = self.infer(d, g, phi, f) {
                    typed
                } else if let ("lam", [body]) = shape(f)? {
                    recover(self, body)?
                } else {
                    self.infer(d, g, phi, f)?
                };
                if shape(&fty)?.0 != "pi"
                    && let Ok((universe, _)) = self.infer(d, g, phi, &fty)
                    && let Ok((target, _)) = self.whnf(d, g, phi, &fty, &universe, FUEL_TYPES)
                    && shape(&target)?.0 == "pi"
                {
                    fi = self.retype_has(d, g, phi, f, &fty, &target, fi)?;
                    fty = target;
                }
                let ("pi", [dom, _]) = shape(&fty)? else {
                    return Err("application expects Pi".into());
                };
                let mut checked = self.check(d, g, phi, a, dom);
                // A lambda's remembered type may come from another use.
                if checked.is_err()
                    && let ("lam", [body]) = shape(f)?
                    && let Ok(recovered) = recover(self, body)
                {
                    (fty, fi) = recovered;
                    let ("pi", [dom, _]) = shape(&fty)? else {
                        unreachable!("recovered a Pi type")
                    };
                    checked = self.check(d, g, phi, a, dom);
                }
                let ai = checked?;
                let ("pi", [_, cod]) = shape(&fty)? else {
                    unreachable!("checked against a Pi domain")
                };
                let (ty, si) = self.f.path.transform(cod, &Op::Subst(0, a.clone()))?;
                let (uty, ti) = self.infer(d, g, phi, &ty)?;
                level(&uty)?;
                (ty, "rhas.app", vec![fi, ai, si, ti])
            }
            (head @ ("fst" | "snd"), [t]) => {
                let (tt, ti) = self.infer_as(d, g, phi, t, "sigma")?;
                let ("sigma", [a, b]) = shape(&tt)? else {
                    return Err("projection expects Sigma".into());
                };
                if head == "fst" {
                    let (ua, ai) = self.infer(d, g, phi, a)?;
                    level(&ua)?;
                    (a.clone(), "rhas.fst", vec![ti, ai])
                } else {
                    let (bt, si) = self
                        .f
                        .path
                        .transform(b, &Op::Subst(0, call("fst", [t.clone()])))?;
                    let (ub, bi) = self.infer(d, g, phi, &bt)?;
                    level(&ub)?;
                    (bt, "rhas.snd", vec![ti, si, bi])
                }
            }
            ("glue-type", [a, f, t, e]) => {
                let (ua, ai) = self.infer(d, g, phi, a)?;
                let l = level(&ua)?;
                let f = Face::parse(f)?;
                let fi = self.f.face(d, &f)?;
                let partial = phi.clone().and(f);
                let ti = self.check(d, g, &partial, t, &u(l))?;
                let (et, def) = self.equiv_type(t, a)?;
                let eti = self.check(d, g, &partial, &et, &u(l))?;
                let ei = self.check(d, g, &partial, e, &et)?;
                (u(l), "rhas.glue-type", vec![ai, fi, ti, def, eti, ei])
            }
            ("glue", [gt, t, a]) => {
                let (ug, gi) = self.infer(d, g, phi, gt)?;
                level(&ug)?;
                let ("glue-type", [base, f, partial_ty, e]) = shape(gt)? else {
                    return Err("glue expects a Glue type annotation".into());
                };
                let partial = phi.clone().and(Face::parse(f)?);
                let ti = self.check(d, g, &partial, t, partial_ty)?;
                let ai = self.check(d, g, phi, a, base)?;
                let mapped = call("app", [call("fst", [e.clone()]), t.clone()]);
                let mi = self.check(d, g, &partial, &mapped, base)?;
                let compat = self.equality(d, g, &partial, &mapped, a, base)?;
                (gt.clone(), "rhas.glue", vec![gi, ti, ai, mi, compat])
            }
            ("unglue", [t]) => {
                let (gt, ti) = self.infer(d, g, phi, t)?;
                let ("glue-type", [a, _, _, _]) = shape(&gt)? else {
                    return Err("unglue expects Glue".into());
                };
                let (ua, ai) = self.infer(d, g, phi, a)?;
                level(&ua)?;
                (a.clone(), "rhas.unglue", vec![ti, ai])
            }
            ("path", [a, b, c]) => {
                let ctx = self.ctx(d, g, phi)?;
                let (g2, gi) = self.f.path.dshiftctx(g, 0)?;
                let (phi2, phi_i) = self.f.path.ftransform(&phi.quote(), &Op::DShift(0))?;
                let (ua, ai) = self.infer(d + 1, &g2, &Face::parse(&phi2)?, a)?;
                let l = level(&ua)?;
                let (a0, s0) = self.f.path.transform(a, &Op::DSubst(0, atom("i0")))?;
                let (a1, s1) = self.f.path.transform(a, &Op::DSubst(0, atom("i1")))?;
                let a0i = self.check(d, g, phi, &a0, &u(l))?;
                let a1i = self.check(d, g, phi, &a1, &u(l))?;
                let bi = self.check(d, g, phi, b, &a0)?;
                let ci = self.check(d, g, phi, c, &a1)?;
                (
                    u(l),
                    "rhas.path",
                    vec![ctx, gi, phi_i, ai, s0, s1, a0i, a1i, bi, ci],
                )
            }
            ("plam", [body]) => {
                let ctx = self.ctx(d, g, phi)?;
                let (g2, gi) = self.f.path.dshiftctx(g, 0)?;
                let (phi2, phi_i) = self.f.path.ftransform(&phi.quote(), &Op::DShift(0))?;
                let phi2 = Face::parse(&phi2)?;
                let (a, ti) = self.infer(d + 1, &g2, &phi2, body)?;
                let (ua, ai) = self.infer(d + 1, &g2, &phi2, &a)?;
                let l = level(&ua)?;
                let (a0, s0) = self.f.path.transform(&a, &Op::DSubst(0, atom("i0")))?;
                let (a1, s1) = self.f.path.transform(&a, &Op::DSubst(0, atom("i1")))?;
                let (t0, st0) = self.f.path.transform(body, &Op::DSubst(0, atom("i0")))?;
                let (t1, st1) = self.f.path.transform(body, &Op::DSubst(0, atom("i1")))?;
                let a0i = self.check(d, g, phi, &a0, &u(l))?;
                let a1i = self.check(d, g, phi, &a1, &u(l))?;
                let t0i = self.check(d, g, phi, &t0, &a0)?;
                let t1i = self.check(d, g, phi, &t1, &a1)?;
                (
                    path(a, t0, t1),
                    "rhas.plam",
                    vec![ctx, gi, phi_i, ai, ti, s0, s1, st0, st1, a0i, a1i, t0i, t1i],
                )
            }
            ("papp", [p, r]) => {
                let (ty, pi) = self.infer_as(d, g, phi, p, "path")?;
                let ("path", [a, _, _]) = shape(&ty)? else {
                    return Err("expected PathP".into());
                };
                let ri = self.f.path.interval(d, r)?;
                let (ar, si) = self.f.path.transform(a, &Op::DSubst(0, r.clone()))?;
                let (uar, ai) = self.infer(d, g, phi, &ar)?;
                level(&uar)?;
                (ar, "rhas.papp", vec![pi, ri, si, ai])
            }
            ("comp", [a, f, tube, base]) => {
                let f = Face::parse(f)?;
                let ctx = self.ctx(d, g, phi)?;
                let (g2, gi) = self.f.path.dshiftctx(g, 0)?;
                let (phi2, phii) = self.f.path.ftransform(&phi.quote(), &Op::DShift(0))?;
                let fi = self.f.face(d, &f)?;
                let (f2, f2i) = self.f.path.ftransform(&f.quote(), &Op::DShift(0))?;
                let phi2 = Face::parse(&phi2)?;
                let tube_phi = phi2.clone().and(Face::parse(&f2)?);
                let (ua, ai) = self.infer(d + 1, &g2, &phi2, a)?;
                let l = level(&ua)?;
                let ti = self.check(d + 1, &g2, &tube_phi, tube, a)?;
                let (a0, s0) = self.f.path.transform(a, &Op::DSubst(0, atom("i0")))?;
                let (a1, s1) = self.f.path.transform(a, &Op::DSubst(0, atom("i1")))?;
                let (t0, st0) = self.f.path.transform(tube, &Op::DSubst(0, atom("i0")))?;
                let a0i = self.check(d, g, phi, &a0, &u(l))?;
                let a1i = self.check(d, g, phi, &a1, &u(l))?;
                let bi = self.check(d, g, phi, base, &a0)?;
                let compat = self.equality(d, g, &phi.clone().and(f), &t0, base, &a0)?;
                (
                    a1,
                    "rhas.comp",
                    vec![
                        ctx, gi, phii, fi, f2i, ai, ti, s0, s1, st0, a0i, a1i, bi, compat,
                    ],
                )
            }
            _ => {
                if let Some((ty, rule, refs)) = self.infer_circle(d, g, phi, t)? {
                    let id = self.has(d, g, phi, t, &ty, &rule, refs);
                    self.remember(d, g, phi, t, &ty, id);
                    return Ok((ty, id));
                }
                if let Some((ty, rule, refs)) = self.infer_declared(d, g, phi, t)? {
                    let id = self.has(d, g, phi, t, &ty, &rule, refs);
                    self.remember(d, g, phi, t, &ty, id);
                    return Ok((ty, id));
                }
                if let Some(found) = self.recall_checked_form(d, g, phi, t)? {
                    return Ok(found);
                }
                return Err(format!("restricted inference needs an annotation for {t}"));
            }
        };
        let id = self.has(d, g, phi, t, &ty, rule, refs);
        self.remember(d, g, phi, t, &ty, id);
        Ok((ty, id))
    }

    pub fn check(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        expected: &Sexp,
    ) -> Result<usize> {
        let key = call(
            "rhas",
            [num(d), g.clone(), phi.quote(), t.clone(), expected.clone()],
        );
        if let Some(id) = self.checked.get(&key) {
            return Ok(*id);
        }
        if self.certified_check_reuse {
            let inferred_key = call("rhas-key", [num(d), g.clone(), phi.quote(), t.clone()]);
            if let Some((actual, id)) = self.inferred.get(&inferred_key)
                && actual == expected
            {
                let id = *id;
                self.checked.insert(key, id);
                return Ok(id);
            }
        }
        if let Some((b, rest)) = self.strengthenable(g, t, Some(expected))
            && let (Ok(t0), Ok(a0)) = (self.lower(t), self.lower(expected))
            && let Ok(id0) = self.check(d, &rest, phi, &t0, &a0)
        {
            let (t2, a2, id) = self.lift(d, &b, &rest, phi, &t0, &a0, id0)?;
            if t2 == *t && a2 == *expected {
                self.checked.insert(key, id);
                return Ok(id);
            }
        }
        let normal = phi.normal();
        let result = if normal != *phi {
            let entails = self.f.entails(d, phi, &normal)?;
            let id = self.check(d, g, &normal, t, expected)?;
            Ok(self.has(d, g, phi, t, expected, "rhas.weaken", vec![entails, id]))
        } else {
            self.check_search(d, g, phi, t, expected)
        };
        if let Ok(id) = result {
            self.checked.insert(key, id);
            // A scoped type checked under false is a valid type there even
            // when its raw syntax has no globally inferable universe.
            if self.type_directed_composition && phi.normal() == Face::False {
                self.remember(d, g, phi, t, expected, id);
            }
        }
        result
    }

    fn check_search(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        expected: &Sexp,
    ) -> Result<usize> {
        if let Ok(absurd) = self.f.entails(d, phi, &Face::False) {
            let ctx = self.ctx(d, g, phi)?;
            let (n, ni) = self.length(g)?;
            let scope = self.scope(d, n, t)?;
            let (ue, ei) = self.infer(d, g, phi, expected)?;
            level(&ue)?;
            return Ok(self.has(
                d,
                g,
                phi,
                t,
                expected,
                "rhas.false",
                vec![ctx, ni, scope, ei, absurd],
            ));
        }
        if let ("system", [s]) = shape(t)? {
            let (ue, ei) = self.infer(d, g, phi, expected)?;
            level(&ue)?;
            let (dom, si) = self.coherent(d, g, phi, s, expected)?;
            let cover = self.f.entails(d, phi, &dom)?;
            let id = self.has(d, g, phi, t, expected, "rhas.system", vec![ei, si, cover]);
            self.remember(d, g, phi, t, expected, id);
            return Ok(id);
        }
        if let Some(id) = self.check_declared(d, g, phi, t, expected)? {
            self.remember(d, g, phi, t, expected, id);
            return Ok(id);
        }
        // An introduction form checked against a type that is not yet in
        // the matching form: normalize the type, check, then convert.
        let former = match shape(t)?.0 {
            "lam" => Some("pi"),
            "pair" => Some("sigma"),
            "plam" => Some("path"),
            _ => None,
        };
        if let Some(former) = former
            && shape(expected)?.0 != former
            && let Ok((universe, _)) = self.infer(d, g, phi, expected)
            && let Ok((target, _)) = self.whnf(d, g, phi, expected, &universe, FUEL_TYPES)
            && shape(&target)?.0 == former
        {
            let id = self.check(d, g, phi, t, &target)?;
            return self.retype_has(d, g, phi, t, &target, expected, id);
        }
        if let ("lam", [body]) = shape(t)? {
            let ("pi", [a, b]) = shape(expected)? else {
                return Err("lambda expects Pi annotation".into());
            };
            let (ua, ai) = self.infer(d, g, phi, a)?;
            level(&ua)?;
            let g2 = cons(a.clone(), g.clone());
            let ti = self.check(d, &g2, phi, body, b)?;
            let (ub, bi) = self.infer(d, &g2, phi, b)?;
            level(&ub)?;
            let id = self.has(d, g, phi, t, expected, "rhas.lam", vec![ai, ti, bi]);
            self.remember(d, g, phi, t, expected, id);
            return Ok(id);
        }
        if let (("plam", [body]), ("path", [a, b, c])) = (shape(t)?, shape(expected)?) {
            let (ut, pti) = self.infer(d, g, phi, expected)?;
            level(&ut)?;
            let (g2, gi) = self.f.path.dshiftctx(g, 0)?;
            let (phi2, phii) = self.f.path.ftransform(&phi.quote(), &Op::DShift(0))?;
            let body_i = self.check(d + 1, &g2, &Face::parse(&phi2)?, body, a)?;
            let (t0, t0i) = self.f.path.transform(body, &Op::DSubst(0, atom("i0")))?;
            let (t1, t1i) = self.f.path.transform(body, &Op::DSubst(0, atom("i1")))?;
            let (a0, a0i) = self.f.path.transform(a, &Op::DSubst(0, atom("i0")))?;
            let (a1, a1i) = self.f.path.transform(a, &Op::DSubst(0, atom("i1")))?;
            let e0 = self.equality(d, g, phi, &t0, b, &a0)?;
            let e1 = self.equality(d, g, phi, &t1, c, &a1)?;
            let id = self.has(
                d,
                g,
                phi,
                t,
                expected,
                "rhas.plam-checked",
                vec![pti, gi, phii, body_i, t0i, t1i, a0i, a1i, e0, e1],
            );
            self.remember(d, g, phi, t, expected, id);
            return Ok(id);
        }
        if let ("pair", [t0, t1]) = shape(t)? {
            let ("sigma", [a, b]) = shape(expected)? else {
                return Err("pair expects Sigma annotation".into());
            };
            let (ua, ai) = self.infer(d, g, phi, a)?;
            level(&ua)?;
            let (ub, bi) = self.infer(d, &cons(a.clone(), g.clone()), phi, b)?;
            let j = level(&ub)?;
            let t0i = self.check(d, g, phi, t0, a)?;
            let (bt, si) = self.f.path.transform(b, &Op::Subst(0, t0.clone()))?;
            let bti = self.check(d, g, phi, &bt, &u(j))?;
            let t1i = self.check(d, g, phi, t1, &bt)?;
            let id = self.has(
                d,
                g,
                phi,
                t,
                expected,
                "rhas.pair",
                vec![ai, bi, t0i, si, bti, t1i],
            );
            self.remember(d, g, phi, t, expected, id);
            return Ok(id);
        }
        let (actual, ti) = self.infer(d, g, phi, t)?;
        if actual == *expected {
            return Ok(ti);
        }
        let (ue, ei) = self.infer(d, g, phi, expected)?;
        level(&ue)?;
        let eq = self.equality(d, g, phi, &actual, expected, &ue)?;
        Ok(self.has(d, g, phi, t, expected, "rhas.conv", vec![ti, eq, ei]))
    }

    // One local path endpoint or full-face composition step. Search is partial.
    fn reduce(&mut self, d: usize, g: &Sexp, phi: &Face, t: &Sexp) -> Result<(Sexp, Sexp, usize)> {
        let (ty, ti) = self.infer(d, g, phi, t)?;
        self.reduce_typed(d, g, phi, t, ty, ti)
    }

    /// Infer the type of `t` and, if it is not yet a `former` type, bring it
    /// to weak-head normal form and convert the typing.
    fn infer_as(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        former: &str,
    ) -> Result<(Sexp, usize)> {
        let (ty, id) = self.infer(d, g, phi, t)?;
        if shape(&ty)?.0 == former {
            return Ok((ty, id));
        }
        let (universe, _) = self.infer(d, g, phi, &ty)?;
        let (target, _) = self.whnf(d, g, phi, &ty, &universe, FUEL_TYPES)?;
        if shape(&target)?.0 != former {
            return Ok((ty, id));
        }
        let id = self.retype_has(d, g, phi, t, &ty, &target, id)?;
        Ok((target, id))
    }

    /// Weak-head normal form of `t : ty` with the equation `t ≡ nf : ty`, by
    /// repeated single steps; at most `fuel` steps. The search is untrusted:
    /// the equation is an ordinary derivation for the kernel to check.
    pub fn whnf(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        ty: &Sexp,
        fuel: usize,
    ) -> Result<(Sexp, usize)> {
        let ti = self.check(d, g, phi, t, ty)?;
        let mut eq = self.eq(d, g, phi, t, t, ty, "req.refl", vec![ti]);
        let mut current = t.clone();
        for _ in 0..fuel {
            let (next, next_ty, step) = self.reduce_at(d, g, phi, &current, ty)?;
            if next == current {
                return Ok((current, eq));
            }
            let step = self.retype_eq(d, g, phi, &current, &next, &next_ty, ty, step)?;
            eq = self.eq(d, g, phi, t, &next, ty, "req.trans", vec![eq, step]);
            current = next;
        }
        Err(format!("evaluation did not finish in {fuel} steps"))
    }

    /// Like `whnf`, but a natural number is normalized under every `suc`, so
    /// a closed term of type nat reaches a numeral.
    pub fn value(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        ty: &Sexp,
        fuel: usize,
    ) -> Result<(Sexp, usize)> {
        let (w, e) = self.whnf(d, g, phi, t, ty, fuel)?;
        // A pair is normalized componentwise.
        if let ("sigma", [a, b]) = shape(ty)?
            && let ("pair", [x, y]) = shape(&w)?
        {
            let (xv, ex) = self.value(d, g, phi, x, a, fuel)?;
            let (by, _) = self.f.path.transform(b, &Op::Subst(0, x.clone()))?;
            let (yv, ey) = self.value(d, g, phi, y, &by, fuel)?;
            if xv != *x || yv != *y {
                let out = call("pair", [xv, yv]);
                let inner = self.congruence(d, g, phi, &w, &out, ty);
                if let Ok(inner) = inner {
                    let _ = (ex, ey);
                    let eq = self.eq(d, g, phi, t, &out, ty, "req.trans", vec![e, inner]);
                    return Ok((out, eq));
                }
            }
        }
        if let Some((out, inner)) = self.value_declared(d, g, phi, &w, ty, fuel)? {
            let eq = self.eq(d, g, phi, t, &out, ty, "req.trans", vec![e, inner]);
            return Ok((out, eq));
        }
        if *ty == atom("nat")
            && let ("suc", [x]) = shape(&w)?
        {
            let (xv, ex) = self.value(d, g, phi, x, ty, fuel)?;
            if xv != *x {
                let out = call("suc", [xv]);
                let inner = self.eq(d, g, phi, &w, &out, ty, "req.suc-cong", vec![ex]);
                let eq = self.eq(d, g, phi, t, &out, ty, "req.trans", vec![e, inner]);
                return Ok((out, eq));
            }
        }
        Ok((w, e))
    }

    /// With `keep_reduct_types`, reduce a term whose type the caller knows
    /// without inferring it again: a reduct may be an introduction form or a
    /// system that cannot be inferred on its own.
    pub(super) fn reduce_at(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        ty: &Sexp,
    ) -> Result<(Sexp, Sexp, usize)> {
        // Reduction builds its equations at the inferred type, so the
        // caller's type is used only when the term cannot be inferred.
        if !self.reduct_types {
            return self.reduce(d, g, phi, t);
        }
        if let Ok((inferred, ti)) = self.infer(d, g, phi, t) {
            return self.reduce_typed(d, g, phi, t, inferred, ti);
        }
        let ti = self.check(d, g, phi, t, ty)?;
        self.reduce_typed(d, g, phi, t, ty.clone(), ti)
    }

    /// β and Σ-β for an annotated head, `app (ann (lam b) Π) r` and
    /// `fst/snd (ann (pair x y) Σ)`. The typing of the bare redex is built
    /// from the annotation (rhas.app, rhas.fst, rhas.snd), so the
    /// introduction form is never inferred on its own.
    fn compute_through_annotation(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        ty: &Sexp,
        ti: usize,
    ) -> Result<Option<(Sexp, Sexp, usize)>> {
        if let ("app", [f, r]) = shape(t)?
            && let ("ann", [lam, pi_ty]) = shape(f)?
            && let ("lam", [body]) = shape(lam)?
            && let ("pi", [a, b]) = shape(pi_ty)?
        {
            let annotated_i = self.check(d, g, phi, f, pi_ty)?;
            let lam_i = self.check(d, g, phi, lam, pi_ty)?;
            let head = self.eq(
                d,
                g,
                phi,
                f,
                lam,
                pi_ty,
                "req.ann",
                vec![annotated_i, lam_i],
            );
            let (ua, ai) = self.infer(d, g, phi, a)?;
            level(&ua)?;
            let ri = self.check(d, g, phi, r, a)?;
            let arg = self.eq(d, g, phi, r, r, a, "req.refl", vec![ri]);
            let (bt, si) = self.f.path.transform(b, &Op::Subst(0, r.clone()))?;
            let (ub, ui) = self.infer(d, g, phi, &bt)?;
            level(&ub)?;
            let bare = call("app", [lam.clone(), r.clone()]);
            let bare_i = self.has(d, g, phi, &bare, &bt, "rhas.app", vec![lam_i, ri, si, ui]);
            let ti = self.retype_has(d, g, phi, t, ty, &bt, ti)?;
            let cong = self.eq(
                d,
                g,
                phi,
                t,
                &bare,
                &bt,
                "req.app-cong",
                vec![head, arg, si, ti, bare_i],
            );
            let g2 = cons(a.clone(), g.clone());
            let bi = self.check(d, &g2, phi, body, b)?;
            let (ubb, bti) = self.infer(d, &g2, phi, b)?;
            level(&ubb)?;
            let (out, oi_s) = self.f.path.transform(body, &Op::Subst(0, r.clone()))?;
            let oi = self.check(d, g, phi, &out, &bt)?;
            let beta = self.eq(
                d,
                g,
                phi,
                &bare,
                &out,
                &bt,
                "req.beta-r",
                vec![ai, bi, bti, ri, oi_s, si, oi],
            );
            let eq = self.eq(d, g, phi, t, &out, &bt, "req.trans", vec![cong, beta]);
            let (out, eq) = self.keep_type(d, g, phi, t, out, &bt, eq)?;
            let eq = self.retype_eq(d, g, phi, t, &out, &bt, ty, eq)?;
            return Ok(Some((out, ty.clone(), eq)));
        }
        if let (head @ ("fst" | "snd"), [inner]) = shape(t)?
            && let ("ann", [pair, sigma_ty]) = shape(inner)?
            && let ("pair", [x, y]) = shape(pair)?
            && let ("sigma", [a, b]) = shape(sigma_ty)?
        {
            let annotated_i = self.check(d, g, phi, inner, sigma_ty)?;
            let pair_i = self.check(d, g, phi, pair, sigma_ty)?;
            let inner_eq = self.eq(
                d,
                g,
                phi,
                inner,
                pair,
                sigma_ty,
                "req.ann",
                vec![annotated_i, pair_i],
            );
            let bare = call(head, [pair.clone()]);
            let (ua, ui) = self.infer(d, g, phi, a)?;
            level(&ua)?;
            // Types below mention `fst (pair x y)`; its typing comes from the
            // annotation and is remembered, so deeper contexts can lift it.
            let first = call("fst", [pair.clone()]);
            let first_i = self.has(d, g, phi, &first, a, "rhas.fst", vec![pair_i, ui]);
            self.remember(d, g, phi, &first, a, first_i);
            if head == "fst" {
                let ti = self.retype_has(d, g, phi, t, ty, a, ti)?;
                let bare_i = first_i;
                let cong = self.eq(
                    d,
                    g,
                    phi,
                    t,
                    &bare,
                    a,
                    "req.fst-cong",
                    vec![inner_eq, ti, bare_i],
                );
                let xi = self.check(d, g, phi, x, a)?;
                let beta = self.eq(d, g, phi, &bare, x, a, "req.fst-beta", vec![pair_i, xi]);
                let eq = self.eq(d, g, phi, t, x, a, "req.trans", vec![cong, beta]);
                let (out, eq) = self.keep_type(d, g, phi, t, x.clone(), a, eq)?;
                let eq = self.retype_eq(d, g, phi, t, &out, a, ty, eq)?;
                return Ok(Some((out, ty.clone(), eq)));
            }
            // snd: the redex's type mentions fst of the annotated pair, the
            // bare one's fst of the pair; the two are converted.
            let (bt, si) = self
                .f
                .path
                .transform(b, &Op::Subst(0, call("fst", [inner.clone()])))?;
            let (bare_t, bsi) = self
                .f
                .path
                .transform(b, &Op::Subst(0, call("fst", [pair.clone()])))?;
            let (ub, ubi) = self.infer(d, g, phi, &bare_t)?;
            level(&ub)?;
            let bare_i = self.has(
                d,
                g,
                phi,
                &bare,
                &bare_t,
                "rhas.snd",
                vec![pair_i, bsi, ubi],
            );
            let bare_i = self.retype_has(d, g, phi, &bare, &bare_t, &bt, bare_i)?;
            let ti = self.retype_has(d, g, phi, t, ty, &bt, ti)?;
            let cong = self.eq(
                d,
                g,
                phi,
                t,
                &bare,
                &bt,
                "req.snd-cong",
                vec![inner_eq, si, ti, bare_i],
            );
            let yi = self.check(d, g, phi, y, &bare_t)?;
            let beta = self.eq(
                d,
                g,
                phi,
                &bare,
                y,
                &bare_t,
                "req.snd-beta",
                vec![pair_i, bsi, yi],
            );
            let beta = self.retype_eq(d, g, phi, &bare, y, &bare_t, &bt, beta)?;
            let eq = self.eq(d, g, phi, t, y, &bt, "req.trans", vec![cong, beta]);
            let (out, eq) = self.keep_type(d, g, phi, t, y.clone(), &bt, eq)?;
            let eq = self.retype_eq(d, g, phi, t, &out, &bt, ty, eq)?;
            return Ok(Some((out, ty.clone(), eq)));
        }
        Ok(None)
    }

    /// `rhas t from` (id) as `rhas t to`, by conversion when they differ.
    #[allow(clippy::too_many_arguments)] // Explicit context, judgment, and proof.
    fn retype_has(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        from: &Sexp,
        to: &Sexp,
        id: usize,
    ) -> Result<usize> {
        if from == to {
            return Ok(id);
        }
        let (u_to, ui) = self.infer(d, g, phi, to)?;
        let conv = self.equality(d, g, phi, from, to, &u_to)?;
        Ok(self.has(d, g, phi, t, to, "rhas.conv", vec![id, conv, ui]))
    }

    fn reduce_typed(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
        ty: Sexp,
        ti: usize,
    ) -> Result<(Sexp, Sexp, usize)> {
        if self.reduct_types
            && let Some(out) = self.compute_through_annotation(d, g, phi, t, &ty, ti)?
        {
            return Ok(out);
        }
        if let ("ann", [value, a]) = shape(t)? {
            let vi = self.check(d, g, phi, value, a)?;
            let eq = self.eq(d, g, phi, t, value, a, "req.ann", vec![ti, vi]);
            return Ok((value.clone(), a.clone(), eq));
        }
        if let ("app", [f, r]) = shape(t)?
            && let ("lam", [body]) = shape(f)?
        {
            if self.typed_beta_reuse {
                let (out, si) = self.f.path.transform(body, &Op::Subst(0, r.clone()))?;
                let oi = self.has(d, g, phi, &out, &ty, "rhas.beta", vec![ti, si]);
                self.remember(d, g, phi, &out, &ty, oi);
                let checked = call(
                    "rhas",
                    [num(d), g.clone(), phi.quote(), out.clone(), ty.clone()],
                );
                self.checked.insert(checked, oi);
                let eq = self.eq(d, g, phi, t, &out, &ty, "req.beta-typed", vec![ti, si, oi]);
                return Ok((out, ty, eq));
            }
            let (ft, _) = self.infer(d, g, phi, f)?;
            let ("pi", [a, b]) = shape(&ft)? else {
                return Err("beta expects Pi".into());
            };
            let (ua, ai) = self.infer(d, g, phi, a)?;
            level(&ua)?;
            let g2 = cons(a.clone(), g.clone());
            let bi = self.check(d, &g2, phi, body, b)?;
            let (ub, bti) = self.infer(d, &g2, phi, b)?;
            level(&ub)?;
            let ri = self.check(d, g, phi, r, a)?;
            let (out, si) = self.f.path.transform(body, &Op::Subst(0, r.clone()))?;
            // The rule states the reduct at b[r]; convert to the caller's type.
            let (c, bsi) = self.f.path.transform(b, &Op::Subst(0, r.clone()))?;
            let oi = self.check(d, g, phi, &out, &c)?;
            let eq = self.eq(
                d,
                g,
                phi,
                t,
                &out,
                &c,
                "req.beta-r",
                vec![ai, bi, bti, ri, si, bsi, oi],
            );
            let eq = self.retype_eq(d, g, phi, t, &out, &c, &ty, eq)?;
            return Ok((out, ty, eq));
        }
        if let ("glue-type", [_, f, partial_ty, _]) = shape(t)?
            && let Ok(cover) = self.f.entails(d, phi, &Face::parse(f)?)
        {
            let oi = self.check(d, g, phi, partial_ty, &ty)?;
            let eq = self.eq(
                d,
                g,
                phi,
                t,
                partial_ty,
                &ty,
                "req.glue-type",
                vec![ti, cover, oi],
            );
            return Ok((partial_ty.clone(), ty, eq));
        }
        if let ("glue", [gt, partial_t, _]) = shape(t)? {
            let ("glue-type", [_, f, partial_ty, _]) = shape(gt)? else {
                return Err("expected Glue type".into());
            };
            if let Ok(cover) = self.f.entails(d, phi, &Face::parse(f)?) {
                let oi = self.check(d, g, phi, partial_t, partial_ty)?;
                let typed_as_partial = self.check(d, g, phi, t, partial_ty)?;
                let eq = self.eq(
                    d,
                    g,
                    phi,
                    t,
                    partial_t,
                    partial_ty,
                    "req.glue-face",
                    vec![ti, cover, oi, typed_as_partial],
                );
                let eq = self.retype_eq(d, g, phi, t, partial_t, partial_ty, &ty, eq)?;
                return Ok((partial_t.clone(), ty, eq));
            }
        }
        if let ("unglue", [value]) = shape(t)? {
            let (mut gt, mut vi) = self.infer(d, g, phi, value)?;
            // A remembered typing may be at a type the Glue type reduced to;
            // an annotated argument is checked at its annotation instead.
            if shape(&gt)?.0 != "glue-type"
                && let ("ann", [_, annotation]) = shape(value)?
                && shape(annotation)?.0 == "glue-type"
            {
                vi = self.check(d, g, phi, value, annotation)?;
                gt = annotation.clone();
            }
            let ("glue-type", [a, f, _, e]) = shape(&gt)? else {
                return Err(format!("expected Glue: unglue {value} : {gt}"));
            };
            if let ("glue", [_, _, base]) = shape(value)? {
                let bi = self.check(d, g, phi, base, a)?;
                let eq = self.eq(d, g, phi, t, base, a, "req.unglue-beta", vec![vi, bi]);
                return Ok((base.clone(), ty, eq));
            }
            if let Ok(cover) = self.f.entails(d, phi, &Face::parse(f)?) {
                let mapped = call("app", [call("fst", [e.clone()]), value.clone()]);
                let mi = self.check(d, g, phi, &mapped, a)?;
                let eq = self.eq(
                    d,
                    g,
                    phi,
                    t,
                    &mapped,
                    a,
                    "req.unglue-face",
                    vec![vi, cover, mi],
                );
                return Ok((mapped, ty, eq));
            }
        }
        if let (head @ ("fst" | "snd"), [pair]) = shape(t)?
            && let ("pair", [a, b]) = shape(pair)?
        {
            let (pty, pi) = self.infer(d, g, phi, pair)?;
            let ("sigma", [dom, cod]) = shape(&pty)? else {
                return Err("projection expects Sigma".into());
            };
            let out = if head == "fst" { a } else { b };
            // The rules state the projection at the Sigma's own component
            // type; the caller's type is reached by conversion afterwards.
            let (rule_ty, refs) = if head == "fst" {
                let oi = self.check(d, g, phi, out, dom)?;
                (dom.clone(), vec![pi, oi])
            } else {
                let (bt, si) = self
                    .f
                    .path
                    .transform(cod, &Op::Subst(0, call("fst", [pair.clone()])))?;
                let oi = self.check(d, g, phi, out, &bt)?;
                (bt, vec![pi, si, oi])
            };
            let eq = self.eq(
                d,
                g,
                phi,
                t,
                out,
                &rule_ty,
                if head == "fst" {
                    "req.fst-beta"
                } else {
                    "req.snd-beta"
                },
                refs,
            );
            let eq = self.retype_eq(d, g, phi, t, out, &rule_ty, &ty, eq)?;
            return Ok((out.clone(), ty, eq));
        }
        if let ("papp", [p, r]) = shape(t)? {
            let (pty, pi) = self.infer(d, g, phi, p)?;
            let ("path", [a, b, c]) = shape(&pty)? else {
                return Err("expected path".into());
            };
            for (one, out) in [(false, b), (true, c)] {
                if let Ok(local) = self.f.endpoint(d, phi, r, one) {
                    let end = atom(if one { "i1" } else { "i0" });
                    let (ar, ari) = self.f.path.transform(a, &Op::DSubst(0, r.clone()))?;
                    let (ae, aei) = self.f.path.transform(a, &Op::DSubst(0, end.clone()))?;
                    if ar != ae {
                        if !self.type_directed_composition {
                            continue;
                        }
                        // The family instances may be equal only on this face.
                        // Use typed path congruence and explicit conversion.
                        let attempt = (|| -> Result<(Sexp, Sexp, usize)> {
                            let (ua, _) = self.infer(d, g, phi, &ar)?;
                            level(&ua)?;
                            self.equality(d, g, phi, &ar, &ae, &ua)?;
                            let mid = papp(p.clone(), end);
                            let pref = self.eq(d, g, phi, p, p, &pty, "req.refl", vec![pi]);
                            let left = self.check(d, g, phi, t, &ar)?;
                            let right = self.check(d, g, phi, &mid, &ar)?;
                            let dim = self.eq(
                                d,
                                g,
                                phi,
                                t,
                                &mid,
                                &ar,
                                "req.papp-cong",
                                vec![pref, local, ari, left, right],
                            );
                            let ae_type = self.check(d, g, phi, &ae, &ua)?;
                            let oi = self.check(d, g, phi, out, &ae)?;
                            let endpoint = self.eq(
                                d,
                                g,
                                phi,
                                &mid,
                                out,
                                &ae,
                                if one { "req.p1-r" } else { "req.p0-r" },
                                vec![pi, aei, ae_type, oi],
                            );
                            let endpoint =
                                self.retype_eq(d, g, phi, &mid, out, &ae, &ar, endpoint)?;
                            let eq =
                                self.eq(d, g, phi, t, out, &ar, "req.trans", vec![dim, endpoint]);
                            let eq = self.retype_eq(d, g, phi, t, out, &ar, &ty, eq)?;
                            Ok((out.clone(), ty.clone(), eq))
                        })();
                        if let Ok(reduced) = attempt {
                            return Ok(reduced);
                        }
                        continue;
                    }
                    let (ua, ai) = self.infer(d, g, phi, &ar)?;
                    level(&ua)?;
                    let mid = papp(p.clone(), end.clone());
                    let dim = self.eq(
                        d,
                        g,
                        phi,
                        t,
                        &mid,
                        &ar,
                        "req.pdim-r",
                        vec![pi, local, ari, aei, ai],
                    );
                    let oi = self.check(d, g, phi, out, &ae)?;
                    let eq = self.eq(
                        d,
                        g,
                        phi,
                        &mid,
                        out,
                        &ae,
                        if one { "req.p1-r" } else { "req.p0-r" },
                        vec![pi, aei, ai, oi],
                    );
                    let id = self.eq(d, g, phi, t, out, &ar, "req.trans", vec![dim, eq]);
                    return Ok((out.clone(), ty, id));
                }
            }
            if let ("plam", [body]) = shape(p)? {
                let ri = self.f.path.interval(d, r)?;
                let (_, ai) = self.f.path.transform(a, &Op::DSubst(0, r.clone()))?;
                let (tr, tri) = self.f.path.transform(body, &Op::DSubst(0, r.clone()))?;
                let oi = self.check(d, g, phi, &tr, &ty)?;
                let eq = self.eq(
                    d,
                    g,
                    phi,
                    t,
                    &tr,
                    &ty,
                    "req.pbeta-r",
                    vec![pi, ri, ai, tri, oi],
                );
                return Ok((tr, ty, eq));
            }
        }
        if let ("comp", [_, f, tube, _]) = shape(t)?
            && let Ok(cover) = self.f.entails(d, phi, &Face::parse(f)?)
        {
            let (t1, s1) = self.f.path.transform(tube, &Op::DSubst(0, atom("i1")))?;
            let oi = self.check(d, g, phi, &t1, &ty)?;
            let eq = self.eq(
                d,
                g,
                phi,
                t,
                &t1,
                &ty,
                "req.comp-face",
                vec![ti, cover, s1, oi],
            );
            return Ok((t1, ty, eq));
        }
        if self.type_directed_composition
            && let Some(out) = self.reduce_composition(d, g, phi, t, &ty, ti)?
        {
            return Ok(out);
        }
        if let Some(reduced) = self.reduce_circle(d, g, phi, t, &ty, ti)? {
            return Ok(reduced);
        }
        if let Some(reduced) = self.reduce_declared(d, g, phi, t, &ty, ti)? {
            return Ok(reduced);
        }
        if let Some(reduced) = self.reduce_eliminator(d, g, phi, t, &ty, ti)? {
            return Ok(reduced);
        }
        let eq = self.eq(d, g, phi, t, t, &ty, "req.refl", vec![ti]);
        Ok((t.clone(), ty, eq))
    }
    pub fn equality(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        a: &Sexp,
        b: &Sexp,
        ty: &Sexp,
    ) -> Result<usize> {
        let key = call(
            "req",
            [
                num(d),
                g.clone(),
                phi.quote(),
                a.clone(),
                b.clone(),
                ty.clone(),
            ],
        );
        if let Some(id) = self.equalities.get(&key) {
            return Ok(*id);
        }
        if !self.equality_active.insert(key.clone()) {
            return Err(format!("cyclic equality search: {a} versus {b} : {ty}"));
        }
        let normal = phi.normal();
        let mut result = if normal != *phi {
            self.f.entails(d, phi, &normal).and_then(|entails| {
                let id = self.equality(d, g, &normal, a, b, ty)?;
                Ok(self.eq(d, g, phi, a, b, ty, "req.weaken", vec![entails, id]))
            })
        } else {
            self.equality_search(d, g, phi, a, b, ty)
        };
        if result.is_err()
            && let Face::Or(left, right) = phi
        {
            result = (|| {
                let cover = self.f.entails(d, phi, phi)?;
                let l = self.equality(d, g, left, a, b, ty)?;
                let r = self.equality(d, g, right, a, b, ty)?;
                Ok(self.eq(d, g, phi, a, b, ty, "req.cases", vec![cover, l, r]))
            })();
        }
        self.equality_active.remove(&key);
        if let Ok(id) = result {
            self.equalities.insert(key, id);
        }
        result
    }

    fn equality_search(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        a: &Sexp,
        b: &Sexp,
        ty: &Sexp,
    ) -> Result<usize> {
        if let Ok(absurd) = self.f.entails(d, phi, &Face::False) {
            let ai = self.check(d, g, phi, a, ty)?;
            let bi = self.check(d, g, phi, b, ty)?;
            return Ok(self.eq(d, g, phi, a, b, ty, "req.false", vec![absurd, ai, bi]));
        }
        if a == b {
            let ti = self.check(d, g, phi, a, ty)?;
            return Ok(self.eq(d, g, phi, a, b, ty, "req.refl", vec![ti]));
        }
        if let ("system", [s]) = shape(a)? {
            let ai = self.check(d, g, phi, a, ty)?;
            let bi = self.check(d, g, phi, b, ty)?;
            let agree = self.agrees(d, g, phi, s, b, ty)?;
            return Ok(self.eq(d, g, phi, a, b, ty, "req.system-eq", vec![ai, bi, agree]));
        }
        if let ("system", [_]) = shape(b)? {
            let id = self.equality(d, g, phi, b, a, ty)?;
            return Ok(self.eq(d, g, phi, a, b, ty, "req.sym", vec![id]));
        }
        // Terms without inferable annotations are checked against the caller's
        // type before any congruence/eta search. This emits object derivations.
        if matches!(shape(a)?.0, "lam" | "pair" | "plam") {
            self.check(d, g, phi, a, ty)?;
        }
        if matches!(shape(b)?.0, "lam" | "pair" | "plam") {
            self.check(d, g, phi, b, ty)?;
        }
        let (aa, aty, ai) = self.reduce_at(d, g, phi, a, ty)?;
        let (bb, bty, bi) = self.reduce_at(d, g, phi, b, ty)?;
        let ai = self.retype_eq(d, g, phi, a, &aa, &aty, ty, ai)?;
        let bi = self.retype_eq(d, g, phi, b, &bb, &bty, ty, bi)?;
        let middle = if aa == bb {
            None
        } else if aa != *a || bb != *b {
            Some(self.equality(d, g, phi, &aa, &bb, ty)?)
        } else {
            return self.congruence(d, g, phi, a, b, ty);
        };
        let left = if let Some(mid) = middle {
            self.eq(d, g, phi, a, &bb, ty, "req.trans", vec![ai, mid])
        } else {
            ai
        };
        let right = self.eq(d, g, phi, &bb, b, ty, "req.sym", vec![bi]);
        Ok(self.eq(d, g, phi, a, b, ty, "req.trans", vec![left, right]))
    }

    #[allow(clippy::too_many_arguments)] // Explicit context, equation, type, and certificate.
    fn retype_eq(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        a: &Sexp,
        b: &Sexp,
        from: &Sexp,
        to: &Sexp,
        id: usize,
    ) -> Result<usize> {
        if from == to {
            return Ok(id);
        }
        // Universes are noncumulative. Attempting to justify U_i = U_j by
        // recursively converting their types would climb the hierarchy forever.
        if matches!((shape(from)?, shape(to)?), (("u", [_]), ("u", [_]))) {
            return Err("distinct universe levels cannot be converted".into());
        }
        let (uty, ti) = self.infer(d, g, phi, to)?;
        level(&uty)?;
        let conv = self.equality(d, g, phi, from, to, &uty)?;
        Ok(self.eq(d, g, phi, a, b, to, "req.conv", vec![id, conv, ti]))
    }
    fn agrees(
        &mut self,
        d: usize,
        g: &Sexp,
        base: &Face,
        s: &Sexp,
        t: &Sexp,
        a: &Sexp,
    ) -> Result<usize> {
        let (rule, refs) = match shape(s)? {
            ("snil", []) => ("agrees.nil", vec![]),
            ("side", [f, branch, rest]) => {
                let phi = base.clone().and(Face::parse(f)?);
                let eq = self.equality(d, g, &phi, branch, t, a)?;
                let tail = self.agrees(d, g, base, rest, t, a)?;
                ("agrees.side", vec![eq, tail])
            }
            _ => return Err("invalid system".into()),
        };
        Ok(self.emit(
            rule,
            refs,
            call(
                "agrees",
                [
                    num(d),
                    g.clone(),
                    base.quote(),
                    s.clone(),
                    t.clone(),
                    a.clone(),
                ],
            ),
        ))
    }

    #[allow(clippy::too_many_arguments)] // Explicit overlap judgment, with both face restrictions.
    fn overlaps(
        &mut self,
        d: usize,
        g: &Sexp,
        base: &Face,
        phi: &Face,
        t: &Sexp,
        s: &Sexp,
        a: &Sexp,
    ) -> Result<usize> {
        let (rule, refs) = match shape(s)? {
            ("snil", []) => ("overlaps.nil", vec![]),
            ("side", [psi, other, rest]) => {
                let overlap = base.clone().and(phi.clone()).and(Face::parse(psi)?);
                let eq = self.equality(d, g, &overlap, t, other, a)?;
                let tail = self.overlaps(d, g, base, phi, t, rest, a)?;
                ("overlaps.side", vec![eq, tail])
            }
            _ => return Err("invalid system".into()),
        };
        Ok(self.emit(
            rule,
            refs,
            call(
                "overlaps",
                [
                    num(d),
                    g.clone(),
                    base.quote(),
                    phi.quote(),
                    t.clone(),
                    s.clone(),
                    a.clone(),
                ],
            ),
        ))
    }
    pub fn coherent(
        &mut self,
        d: usize,
        g: &Sexp,
        base: &Face,
        s: &Sexp,
        a: &Sexp,
    ) -> Result<(Face, usize)> {
        let (dom, rule, refs) = match shape(s)? {
            ("snil", []) => (Face::False, "coherent.nil", vec![self.ctx(d, g, base)?]),
            ("side", [f, t, rest]) => {
                let phi = Face::parse(f)?;
                let fi = self.f.face(d, &phi)?;
                let ti = self.check(d, g, &base.clone().and(phi.clone()), t, a)?;
                let (rest_dom, si) = self.coherent(d, g, base, rest, a)?;
                let overlaps = self.overlaps(d, g, base, &phi, t, rest, a)?;
                (
                    phi.or(rest_dom),
                    "coherent.side",
                    vec![fi, ti, si, overlaps],
                )
            }
            _ => return Err("invalid system".into()),
        };
        let id = self.emit(
            rule,
            refs,
            call(
                "coherent",
                [
                    num(d),
                    g.clone(),
                    base.quote(),
                    s.clone(),
                    a.clone(),
                    dom.quote(),
                ],
            ),
        );
        Ok((dom, id))
    }

    /// A type for a term that needs an annotation, from a context where it was
    /// checked: Γ extended by ordinary binders (types shifted), or Γ under
    /// one more dimension binder (types dimension-shifted). The candidate is
    /// checked again here, so a wrong one only fails.
    fn recall_checked_form(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        t: &Sexp,
    ) -> Result<Option<(Sexp, usize)>> {
        if !self.reduct_types {
            return Ok(None);
        }
        let known = self.checked_forms.get(t).cloned().unwrap_or_default();
        for (d0, g0, a0) in known {
            let candidate = if d0 == d {
                let mut tail = g.clone();
                let mut extra = 0;
                while tail != g0 {
                    let ("cons", [_, rest]) = shape(&tail)? else {
                        break;
                    };
                    tail = rest.clone();
                    extra += 1;
                }
                if tail != g0 || extra == 0 {
                    continue;
                }
                let mut a = a0;
                for _ in 0..extra {
                    a = self.f.path.transform(&a, &Op::Shift(0))?.0;
                }
                a
            } else if d == d0 + 1 && self.f.path.dshiftctx(&g0, 0)?.0 == *g {
                self.f.path.transform(&a0, &Op::DShift(0))?.0
            } else {
                continue;
            };
            if let Ok(id) = self.check(d, g, phi, t, &candidate) {
                return Ok(Some((candidate, id)));
            }
        }
        Ok(None)
    }
    fn remember(&mut self, d: usize, g: &Sexp, phi: &Face, t: &Sexp, a: &Sexp, id: usize) {
        if self.reduct_types && matches!(shape(t), Ok(("lam" | "pair" | "plam", _))) {
            let known = self.checked_forms.entry(t.clone()).or_default();
            let entry = (d, g.clone(), a.clone());
            if !known.contains(&entry) {
                known.push(entry);
            }
        }
        let key = call("rhas-key", [num(d), g.clone(), phi.quote(), t.clone()]);
        if let Some(hints) = &mut self.restriction_hints {
            let hint_key = call("typing-hints", [num(d), g.clone(), t.clone()]);
            let candidates = hints.entry(hint_key).or_default();
            if !candidates.iter().any(|(f, _)| f == phi) {
                candidates.push((phi.clone(), key.clone()));
            }
        }
        self.inferred.insert(key, (a.clone(), id));
    }

    pub fn export_has(&mut self, d: usize, g: &Sexp, t: &Sexp, a: &Sexp) -> Result<usize> {
        let id = self.check(d, g, &Face::True, t, a)?;
        Ok(self.emit(
            "rhas.export",
            vec![id],
            call("has", [num(d), g.clone(), t.clone(), a.clone()]),
        ))
    }
}

pub fn system(sides: &[(Face, Sexp)]) -> Sexp {
    call(
        "system",
        [sides.iter().rev().fold(atom("snil"), |rest, (phi, t)| {
            call("side", [phi.quote(), t.clone(), rest])
        })],
    )
}

pub fn restricted_demo() -> Result<RestrictedProducer> {
    use crate::cubical::engine::path_frontend::{dim, v};
    let mut p = RestrictedProducer::default();
    let nil = atom("nil");
    let nat = atom("nat");
    let zero = atom("zero");
    let top = Face::True;
    let end0 = Face::End(0, false);
    let boundary = end0.clone().or(Face::End(0, true));

    let (_, id) = p.f.path.ftransform(
        &end0.quote(),
        &Op::DSubst(0, call("meet", [dim(0), dim(1)])),
    )?;
    p.f.path.p.result("compound-face-substitution", id);

    // P : Path U0 Nat Nat. zero : P i holds under i=0, but not globally.
    let pty = path(u(0), nat.clone(), nat.clone());
    let gp = cons(pty.clone(), nil.clone());
    let pi = papp(v(0), dim(0));
    let id = p.check(1, &gp, &end0, &zero, &pi)?;
    p.f.path.p.result("genuinely-local-typing", id);
    // y : Path (P i) zero zero itself forms only under the restriction.
    let local_ty = path(papp(v(0), dim(1)), zero.clone(), zero.clone());
    let local_ctx = cons(local_ty, gp.clone());
    let id = p.ctx(1, &local_ctx, &end0)?;
    p.f.path.p.result("genuinely-local-context", id);

    // A system defined on the endpoint boundary, whose two values differ.
    let gx = cons(nat.clone(), nil.clone());
    let sys = system(&[(end0.clone(), zero.clone()), (Face::End(0, true), v(0))]);
    let id = p.check(1, &gx, &boundary, &sys, &nat)?;
    p.f.path.p.result("boundary-system", id);
    let total = system(&[(Face::True, zero.clone()), (end0.clone(), zero.clone())]);
    let id = p.export_has(1, &nil, &total, &nat)?;
    p.f.path.p.result("total-system", id);

    let full_comp = call(
        "comp",
        [nat.clone(), top.quote(), zero.clone(), zero.clone()],
    );
    let id = p.export_has(0, &nil, &full_comp, &nat)?;
    p.f.path.p.result("composition-typing", id);
    let id = p.equality(0, &nil, &top, &full_comp, &zero, &nat)?;
    let id = p.emit(
        "req.export",
        vec![id],
        call(
            "eq",
            [num(0), nil.clone(), full_comp, zero.clone(), nat.clone()],
        ),
    );
    p.f.path.p.result("composition-full-face", id);

    // P : Path U0 Nat Nat, q : PathP (i -> P i) zero zero.
    // Compose in the genuinely nonconstant family P i with q as the tube.
    let qty = path(papp(v(0), dim(0)), zero.clone(), zero.clone());
    let gq = cons(qty, gp);
    let a = papp(v(1), dim(0));
    // A two-branch tube, defined on the ambient boundary, with the fresh
    // composition direction at index 0 and ambient dimension at index 1.
    let tube = system(&[
        (Face::End(1, false), papp(v(0), dim(0))),
        (Face::End(1, true), papp(v(0), dim(0))),
    ]);
    let comp = call("comp", [a, boundary.quote(), tube, zero.clone()]);
    let a1 = papp(v(1), atom("i1"));
    let id = p.export_has(1, &gq, &comp, &a1)?;
    p.f.path.p.result("dependent-composition", id);
    let id = p.equality(1, &gq, &boundary, &comp, &zero, &a1)?;
    p.f.path.p.result("dependent-composition-boundary", id);
    Ok(p)
}
