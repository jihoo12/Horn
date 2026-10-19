//! Untrusted proof producer. Lambda domains are annotations erased by quote().
//! Equality search is deliberately limited to chains of root beta steps.
use crate::cubical::engine::term::{Result, Sexp, atom, call};

#[derive(Clone, Debug)]
pub enum E {
    U(usize),
    V(usize),
    Nat,
    Zero,
    Pi(Box<E>, Box<E>),
    Lam(Box<E>, Box<E>),
    App(Box<E>, Box<E>),
}

pub fn pi(a: E, b: E) -> E {
    E::Pi(Box::new(a), Box::new(b))
}
pub fn lam(a: E, b: E) -> E {
    E::Lam(Box::new(a), Box::new(b))
}
pub fn app(f: E, a: E) -> E {
    E::App(Box::new(f), Box::new(a))
}

pub fn number(n: usize) -> Sexp {
    (0..n).fold(atom("z"), |x, _| call("s", [x]))
}

impl E {
    pub fn quote(&self) -> Sexp {
        match self {
            Self::U(n) => call("u", [number(*n)]),
            Self::V(n) => call("v", [number(*n)]),
            Self::Nat => atom("nat"),
            Self::Zero => atom("zero"),
            Self::Pi(a, b) => call("pi", [a.quote(), b.quote()]),
            Self::Lam(_, b) => call("lam", [b.quote()]),
            Self::App(f, a) => call("app", [f.quote(), a.quote()]),
        }
    }

    fn shift(&self, k: usize) -> E {
        match self {
            Self::V(n) => Self::V(if *n >= k { n + 1 } else { *n }),
            Self::Pi(a, b) => pi(a.shift(k), b.shift(k + 1)),
            Self::Lam(a, b) => lam(a.shift(k), b.shift(k + 1)),
            Self::App(f, a) => app(f.shift(k), a.shift(k)),
            _ => self.clone(),
        }
    }

    fn subst(&self, k: usize, r: &E) -> E {
        match self {
            Self::V(n) if *n == k => r.clone(),
            Self::V(n) => Self::V(if *n > k { n - 1 } else { *n }),
            Self::Pi(a, b) => pi(a.subst(k, r), b.subst(k + 1, &r.shift(0))),
            Self::Lam(a, b) => lam(a.subst(k, r), b.subst(k + 1, &r.shift(0))),
            Self::App(f, a) => app(f.subst(k, r), a.subst(k, r)),
            _ => self.clone(),
        }
    }
}

fn context(g: &[E]) -> Sexp {
    g.iter()
        .fold(atom("nil"), |tail, a| call("cons", [a.quote(), tail]))
}

fn extend(g: &[E], a: &E) -> Vec<E> {
    let mut out = g.to_vec();
    out.push(a.clone());
    out
}

fn universe(a: &E) -> Result<usize> {
    if let E::U(n) = a {
        Ok(*n)
    } else {
        Err(format!("expected universe, got {}", a.quote()))
    }
}

#[derive(Default)]
pub struct Producer {
    // In archive mode use judgment(id), rather than reading the third field.
    pub steps: Vec<(String, Vec<usize>, Sexp)>,
    cache: crate::cubical::engine::term::FastMap<Sexp, usize>,
    results: Vec<(String, usize)>,
    // Judgments are hash-consed, so storing them is cheap; this flag only
    // turns on progress messages for large runs.
    archive: Option<()>,
}

impl Producer {
    #[allow(dead_code)] // Only large-certificate producers enable this mode.
    pub fn archive_judgments(&mut self) {
        self.archive = Some(());
    }

    #[allow(dead_code)] // Deep producers read judgments through this accessor.
    pub fn judgment(&self, id: usize) -> Sexp {
        self.steps[id].2.clone()
    }

    #[allow(dead_code)]
    pub fn known_judgment(&self, judgment: &Sexp) -> Option<usize> {
        self.cache.get(judgment).copied()
    }
    pub fn emit(&mut self, rule: &str, refs: Vec<usize>, judgment: Sexp) -> usize {
        if let Some(id) = self.cache.get(&judgment) {
            return *id;
        }
        let id = self.steps.len();
        if self.archive.is_some() && id > 0 && id.is_multiple_of(100_000) {
            eprintln!("GENERATING (not checked): {id} proof steps");
            if std::env::var_os("HORN_PROFILE").is_some() && id.is_multiple_of(500_000) {
                let mut h = std::collections::HashMap::<&str, usize>::new();
                for (r, _, _) in &self.steps[id - 500_000..] {
                    *h.entry(r.as_str()).or_default() += 1;
                }
                let mut v: Vec<_> = h.into_iter().collect();
                v.sort_by(|a, b| b.1.cmp(&a.1));
                eprintln!("PROFILE {:?}", &v[..v.len().min(20)]);
            }
        }
        self.cache.insert(judgment.clone(), id);
        self.steps.push((rule.to_owned(), refs, judgment));
        id
    }

    pub fn result(&mut self, name: &str, id: usize) {
        self.results.push((name.to_owned(), id));
    }

    pub fn results(&self) -> &[(String, usize)] {
        &self.results
    }

    pub fn text(&self) -> String {
        let mut out = String::new();
        for (i, (rule, refs, j)) in self.steps.iter().enumerate() {
            let refs = Sexp::List(refs.iter().map(|n| atom(n.to_string())).collect());
            out.push_str(&format!("(step {i} {rule} {refs} {j})\n"));
        }
        for (name, id) in &self.results {
            out.push_str(&format!("(result {name} {id})\n"));
        }
        out
    }

    // Remove unsuccessful search branches and renumber only earlier references.
    // This is producer-side compression; the checker receives an ordinary proof.
    #[allow(dead_code)]
    pub fn reachable_text(&self) -> String {
        let mut bytes = Vec::new();
        self.write_reachable(&mut bytes)
            .expect("write proof to memory");
        String::from_utf8(bytes).expect("producer emitted UTF-8")
    }
    #[allow(dead_code)]
    pub fn write_reachable(&self, mut out: impl std::io::Write) -> std::io::Result<usize> {
        let mut keep = vec![false; self.steps.len()];
        let mut pending: Vec<_> = self.results.iter().map(|(_, i)| *i).collect();
        while let Some(i) = pending.pop() {
            if keep[i] {
                continue;
            }
            keep[i] = true;
            pending.extend(self.steps[i].1.iter().copied());
        }
        if std::env::var_os("HORN_PROFILE").is_some() {
            let mut h = std::collections::HashMap::<&str, usize>::new();
            for (i, (r, _, _)) in self.steps.iter().enumerate() {
                if !keep[i] {
                    *h.entry(r.as_str()).or_default() += 1;
                }
            }
            let mut v: Vec<_> = h.into_iter().collect();
            v.sort_by(|a, b| b.1.cmp(&a.1));
            eprintln!("UNREACHABLE {} {:?}", keep.iter().filter(|k| !**k).count(), &v[..v.len().min(25)]);
        }
        let mut next = 0;
        let ids: Vec<_> = keep
            .iter()
            .map(|k| {
                if *k {
                    let i = next;
                    next += 1;
                    Some(i)
                } else {
                    None
                }
            })
            .collect();
        let mut names = std::collections::HashMap::new();
        for (i, (rule, refs, j)) in self.steps.iter().enumerate() {
            let Some(id) = ids[i] else {
                continue;
            };
            let refs: Vec<String> = refs
                .iter()
                .map(|r| ids[*r].expect("retained earlier premise").to_string())
                .collect();
            // The judgment's arguments refer to shared definitions, so the
            // text grows with the number of distinct subterms, not their size.
            let Sexp::List(parts) = j else {
                writeln!(out, "(step {id} {rule} ({}) {j})", refs.join(" "))?;
                continue;
            };
            let mut judgment = format!("({}", parts[0]);
            for arg in &parts[1..] {
                judgment.push(' ');
                judgment.push_str(&shared(arg, &mut names, &mut out)?);
            }
            judgment.push(')');
            writeln!(out, "(step {id} {rule} ({}) {judgment})", refs.join(" "))?;
        }
        for (name, id) in &self.results {
            writeln!(
                out,
                "(result {name} {})",
                ids[*id].expect("retained result")
            )?;
        }
        Ok(next)
    }

    fn le(&mut self, m: usize, n: usize) -> Result<usize> {
        if m > n {
            return Err("false <= premise".into());
        }
        let (rule, refs) = if m == 0 {
            ("le.z", vec![])
        } else {
            ("le.s", vec![self.le(m - 1, n - 1)?])
        };
        Ok(self.emit(rule, refs, call("le", [number(m), number(n)])))
    }

    fn lt(&mut self, m: usize, n: usize) -> Result<usize> {
        if m >= n {
            return Err("false < premise".into());
        }
        let (rule, refs) = if m == 0 {
            ("lt.z", vec![])
        } else {
            ("lt.s", vec![self.lt(m - 1, n - 1)?])
        };
        Ok(self.emit(rule, refs, call("lt", [number(m), number(n)])))
    }

    fn max(&mut self, m: usize, n: usize) -> usize {
        let (rule, refs) = if m == 0 {
            ("max.z", vec![])
        } else if n == 0 {
            ("max.sz", vec![])
        } else {
            ("max.ss", vec![self.max(m - 1, n - 1)])
        };
        self.emit(
            rule,
            refs,
            call("max", [number(m), number(n), number(m.max(n))]),
        )
    }

    pub fn shift(&mut self, t: &E, k: usize) -> Result<(E, usize)> {
        let out = t.shift(k);
        let (rule, refs) = match t {
            E::U(_) => ("shift.u", vec![]),
            E::Nat => ("shift.nat", vec![]),
            E::Zero => ("shift.zero", vec![]),
            E::V(n) if *n < k => ("shift.v.lt", vec![self.lt(*n, k)?]),
            E::V(n) => ("shift.v.ge", vec![self.le(k, *n)?]),
            E::Pi(a, b) => (
                "shift.pi",
                vec![self.shift(a, k)?.1, self.shift(b, k + 1)?.1],
            ),
            E::Lam(_, b) => ("shift.lam", vec![self.shift(b, k + 1)?.1]),
            E::App(f, a) => ("shift.app", vec![self.shift(f, k)?.1, self.shift(a, k)?.1]),
        };
        let id = self.emit(
            rule,
            refs,
            call("shift", [t.quote(), number(k), out.quote()]),
        );
        Ok((out, id))
    }

    pub fn subst(&mut self, t: &E, k: usize, r: &E) -> Result<(E, usize)> {
        let out = t.subst(k, r);
        let (rule, refs) = match t {
            E::U(_) => ("subst.u", vec![]),
            E::Nat => ("subst.nat", vec![]),
            E::Zero => ("subst.zero", vec![]),
            E::V(n) if *n == k => ("subst.v.hit", vec![]),
            E::V(n) if *n < k => ("subst.v.lt", vec![self.lt(*n, k)?]),
            E::V(n) => ("subst.v.gt", vec![self.lt(k, *n)?]),
            E::Pi(a, b) => {
                let a_id = self.subst(a, k, r)?.1;
                let (r2, shift) = self.shift(r, 0)?;
                ("subst.pi", vec![a_id, shift, self.subst(b, k + 1, &r2)?.1])
            }
            E::Lam(_, b) => {
                let (r2, shift) = self.shift(r, 0)?;
                ("subst.lam", vec![shift, self.subst(b, k + 1, &r2)?.1])
            }
            E::App(f, a) => (
                "subst.app",
                vec![self.subst(f, k, r)?.1, self.subst(a, k, r)?.1],
            ),
        };
        let id = self.emit(
            rule,
            refs,
            call("subst", [t.quote(), number(k), r.quote(), out.quote()]),
        );
        Ok((out, id))
    }

    fn ctx(&mut self, g: &[E]) -> Result<usize> {
        let (rule, refs) = if let Some((a, tail)) = g.split_last() {
            let tail_id = self.ctx(tail)?;
            let (ty, a_id) = self.infer(tail, a)?;
            universe(&ty)?;
            ("ctx.cons", vec![tail_id, a_id])
        } else {
            ("ctx.nil", vec![])
        };
        Ok(self.emit(rule, refs, call("ctx", [context(g)])))
    }

    fn lookup(&mut self, g: &[E], n: usize) -> Result<(E, usize)> {
        let (a, tail) = g.split_last().ok_or("unbound variable")?;
        let (ty, rule, refs) = if n == 0 {
            let (ty, shift) = self.shift(a, 0)?;
            (ty, "lookup.z", vec![shift])
        } else {
            let (ty, prior) = self.lookup(tail, n - 1)?;
            let (ty, shift) = self.shift(&ty, 0)?;
            (ty, "lookup.s", vec![prior, shift])
        };
        let id = self.emit(
            rule,
            refs,
            call("lookup", [context(g), number(n), ty.quote()]),
        );
        Ok((ty, id))
    }

    pub fn infer(&mut self, g: &[E], t: &E) -> Result<(E, usize)> {
        let (ty, rule, refs) = match t {
            E::U(n) => (E::U(n + 1), "type.u", vec![self.ctx(g)?]),
            E::Nat => (E::U(0), "type.nat", vec![self.ctx(g)?]),
            E::Zero => (E::Nat, "type.zero", vec![self.ctx(g)?]),
            E::V(n) => {
                let ctx = self.ctx(g)?;
                let (a, lookup) = self.lookup(g, *n)?;
                (a, "type.v", vec![ctx, lookup])
            }
            E::Pi(a, b) => {
                let (u, a_id) = self.infer(g, a)?;
                let (v, b_id) = self.infer(&extend(g, a), b)?;
                let i = universe(&u)?;
                let j = universe(&v)?;
                (E::U(i.max(j)), "type.pi", vec![a_id, b_id, self.max(i, j)])
            }
            E::Lam(a, body) => {
                let (u, a_id) = self.infer(g, a)?;
                universe(&u)?;
                let ext = extend(g, a);
                let (b, body_id) = self.infer(&ext, body)?;
                let (v, b_id) = self.infer(&ext, &b)?;
                universe(&v)?;
                (pi(*a.clone(), b), "type.lam", vec![a_id, body_id, b_id])
            }
            E::App(f, a) => {
                let (fty, f_id) = self.infer(g, f)?;
                let E::Pi(domain, codomain) = fty else {
                    return Err("frontend only applies functions with a syntactic Pi type".into());
                };
                let a_id = self.check(g, a, &domain)?;
                let (ty, subst) = self.subst(&codomain, 0, a)?;
                (ty, "type.app", vec![f_id, a_id, subst])
            }
        };
        let id = self.emit(rule, refs, call("has", [context(g), t.quote(), ty.quote()]));
        Ok((ty, id))
    }

    pub fn check(&mut self, g: &[E], t: &E, expected: &E) -> Result<usize> {
        let (actual, t_id) = self.infer(g, t)?;
        if actual.quote() == expected.quote() {
            return Ok(t_id);
        }
        let eq = self.equal(g, &actual, expected)?;
        let (u, expected_id) = self.infer(g, expected)?;
        universe(&u)?;
        Ok(self.emit(
            "type.conv",
            vec![t_id, eq, expected_id],
            call("has", [context(g), t.quote(), expected.quote()]),
        ))
    }

    fn equality(&mut self, g: &[E], a: &E, b: &E, ty: &E, rule: &str, refs: Vec<usize>) -> usize {
        self.emit(
            rule,
            refs,
            call("eq", [context(g), a.quote(), b.quote(), ty.quote()]),
        )
    }

    fn reduce(&mut self, g: &[E], t: &E, fuel: usize) -> Result<(E, E, usize)> {
        if fuel == 0 {
            return Err("root beta reduction fuel exhausted".into());
        }
        if let E::App(f, r) = t
            && let E::Lam(a, body) = &**f
        {
            let (_, a_id) = self.infer(g, a)?;
            let ext = extend(g, a);
            let (b, body_id) = self.infer(&ext, body)?;
            let (_, b_id) = self.infer(&ext, &b)?;
            let r_id = self.check(g, r, a)?;
            let (out, out_id) = self.subst(body, 0, r)?;
            let (ty, ty_id) = self.subst(&b, 0, r)?;
            let beta = self.equality(
                g,
                t,
                &out,
                &ty,
                "eq.beta",
                vec![a_id, body_id, b_id, r_id, out_id, ty_id],
            );
            let (nf, nf_ty, rest) = self.reduce(g, &out, fuel - 1)?;
            if ty.quote() != nf_ty.quote() {
                return Err(
                    "frontend needs equality conversion between reduction result types".into(),
                );
            }
            let total = self.equality(g, t, &nf, &ty, "eq.trans", vec![beta, rest]);
            return Ok((nf, ty, total));
        }
        let (ty, proof) = self.infer(g, t)?;
        let refl = self.equality(g, t, t, &ty, "eq.refl", vec![proof]);
        Ok((t.clone(), ty, refl))
    }

    fn equal(&mut self, g: &[E], a: &E, b: &E) -> Result<usize> {
        let (na, ta, pa) = self.reduce(g, a, 128)?;
        let (nb, tb, pb) = self.reduce(g, b, 128)?;
        if na.quote() != nb.quote() || ta.quote() != tb.quote() {
            return Err(
                "frontend equality search did not find matching root-beta normal forms".into(),
            );
        }
        let sym = self.equality(g, &nb, b, &tb, "eq.sym", vec![pb]);
        Ok(self.equality(g, a, b, &ta, "eq.trans", vec![pa, sym]))
    }
}

pub fn dtt_demo() -> Result<Producer> {
    use E::*;
    let mut p = Producer::default();
    let identity = lam(U(0), lam(V(0), V(0)));
    let id_type = pi(U(0), pi(V(0), V(1)));
    let (_, formation) = p.infer(&[], &id_type)?;
    p.result("dependent-pi", formation);
    let identity_id = p.check(&[], &identity, &id_type)?;
    p.result("dependent-id", identity_id);
    let applied = app(app(identity, Nat), Zero);
    let applied_id = p.check(&[], &applied, &Nat)?;
    p.result("dependent-application", applied_id);
    let redex_type = app(lam(U(0), V(0)), Nat);
    let conv = p.check(&[], &Zero, &redex_type)?;
    p.result("explicit-conversion", conv);
    let conversion_app = app(lam(redex_type, V(0)), Zero);
    let (_, conversion_app_id) = p.infer(&[], &conversion_app)?;
    p.result("application-with-conversion", conversion_app_id);
    let (_, hierarchy) = p.infer(&[], &U(0))?;
    p.result("universe-hierarchy", hierarchy);
    // Γ = A:U0, x:A. Replacing a variable under λ must not capture x.
    let (_, capture) = p.subst(&lam(Nat, V(1)), 0, &V(0))?;
    p.result("capture-avoidance", capture);
    // A dependent codomain must preserve its bound x and substitute free A.
    let (_, dependent_subst) = p.subst(&pi(V(0), V(1)), 0, &Nat)?;
    p.result("dependent-substitution", dependent_subst);
    let (_, _, beta) = p.reduce(&[U(0), V(0)], &app(lam(Nat, lam(V(2), V(2))), Zero), 128)?;
    p.result("open-dependent-beta", beta);
    Ok(p)
}

/// The text for `t` in a compact certificate: an atom itself, or `?dN` for a
/// compound term, writing its `def` (after those of its subterms) once.
fn shared(
    t: &Sexp,
    names: &mut std::collections::HashMap<Sexp, usize>,
    out: &mut impl std::io::Write,
) -> std::io::Result<String> {
    let Sexp::List(xs) = t else {
        return Ok(t.to_string());
    };
    if let Some(n) = names.get(t) {
        return Ok(format!("?d{n}"));
    }
    let mut text = format!("({}", xs[0]);
    for x in &xs[1..] {
        text.push(' ');
        text.push_str(&shared(x, names, out)?);
    }
    text.push(')');
    let n = names.len();
    writeln!(out, "(def ?d{n} {text})")?;
    names.insert(t.clone(), n);
    Ok(format!("?d{n}"))
}
