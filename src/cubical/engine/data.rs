//! User-declared data types. A declaration generates an explicit theory
//! fragment (formation, constructors, a dependent eliminator, computation,
//! congruence and composition) that is appended to the selected theory and
//! shipped with every certificate that uses it; nothing is built in.
//!
//! Constructor arguments may only be bool, nat, earlier data types, or the
//! type itself. Every such type is discrete (a constant presheaf in the
//! cubical-set model), so the declared type is discrete too and composition
//! in it may return its base. Without function or universe arguments the
//! declaration is trivially strictly positive.
use super::term::{Sexp, atom, call};
use std::cell::RefCell;
use std::fmt::Write;
use std::rc::Rc;

pub struct Ctor {
    /// The user's name and the theory symbol.
    pub name: String,
    pub symbol: String,
    /// Argument types as core terms (constants such as `nat` or `ty/T`).
    pub args: Vec<Sexp>,
    /// Indices of the arguments whose type is the declared type itself.
    pub recursive: Vec<usize>,
}

pub struct Data {
    pub name: String,
    pub ty: String,
    pub elim: String,
    pub ctors: Vec<Ctor>,
}

thread_local! {
    static DATA: RefCell<Vec<Rc<Data>>> = const { RefCell::new(Vec::new()) };
}

pub fn clear() {
    DATA.with(|d| d.borrow_mut().clear());
}

pub fn register(data: Data) -> Rc<Data> {
    let data = Rc::new(data);
    DATA.with(|d| d.borrow_mut().push(data.clone()));
    data
}

fn find(pred: impl Fn(&Data) -> bool) -> Option<Rc<Data>> {
    DATA.with(|d| d.borrow().iter().find(|x| pred(x)).cloned())
}

pub fn by_name(name: &str) -> Option<Rc<Data>> {
    find(|d| d.name == name)
}
pub fn by_type(symbol: &str) -> Option<Rc<Data>> {
    find(|d| d.ty == symbol)
}
pub fn by_elim(symbol: &str) -> Option<Rc<Data>> {
    find(|d| d.elim == symbol)
}
pub fn by_ctor(symbol: &str) -> Option<(Rc<Data>, usize)> {
    let data = find(|d| d.ctors.iter().any(|c| c.symbol == symbol))?;
    let i = data.ctors.iter().position(|c| c.symbol == symbol)?;
    Some((data, i))
}
pub fn by_ctor_name(name: &str) -> Option<(Rc<Data>, usize)> {
    let data = find(|d| d.ctors.iter().any(|c| c.name == name))?;
    let i = data.ctors.iter().position(|c| c.name == name)?;
    Some((data, i))
}
/// Any declared head: a type, constructor or eliminator symbol.
pub fn is_declared(symbol: &str) -> bool {
    by_type(symbol).is_some() || by_elim(symbol).is_some() || by_ctor(symbol).is_some()
}

fn unary(n: usize) -> String {
    let mut s = "z".to_owned();
    for _ in 0..n {
        s = format!("(s {s})");
    }
    s
}

impl Data {
    /// The method types' shape: for constructor `i`, how many shifts each
    /// induction hypothesis and the codomain need, and the variable they
    /// substitute for the motive's variable. Shared by the rule text and the
    /// engine's inference so that both state the same premises in order.
    pub fn method_plan(&self, i: usize) -> (Vec<(usize, usize)>, usize, Vec<usize>) {
        let c = &self.ctors[i];
        let (n, r) = (c.args.len(), c.recursive.len());
        let ihs = c
            .recursive
            .iter()
            .enumerate()
            .map(|(q, &j)| (n + q, n - 1 - j + q))
            .collect();
        let codomain_args = (0..n).map(|k| n - 1 - k + r).collect();
        (ihs, n + r, codomain_args)
    }

    /// The generated theory fragment.
    pub fn theory(&self) -> String {
        let (t, e) = (&self.ty, &self.elim);
        let mut out = String::new();
        let w = &mut out;
        let k = self.ctors.len();
        let methods: Vec<String> = (0..k).map(|i| format!("?m{i}")).collect();
        let ms = methods.join(" ");
        let _ = writeln!(w, "; data {} (generated)", self.name);
        let _ = writeln!(w, "(ctor {t} () Tm)");
        for c in &self.ctors {
            let sorts = vec!["Tm"; c.args.len()].join(" ");
            let _ = writeln!(w, "(ctor {} ({sorts}) Tm)", c.symbol);
        }
        let _ = writeln!(w, "(ctor {e} ({}) Tm)", vec!["Tm"; k + 2].join(" "));
        // Structure: scope, shifts and substitutions.
        let _ = writeln!(w, "(rule scope.{t} () (scoped ?d ?n {t}))");
        for op in ["shift", "dshift"] {
            let _ = writeln!(w, "(rule {op}.{t} () ({op} {t} ?k {t}))");
        }
        for op in ["subst", "dsubst"] {
            let _ = writeln!(w, "(rule {op}.{t} () ({op} {t} ?k ?r {t}))");
        }
        for c in &self.ctors {
            let s = &c.symbol;
            let a: Vec<String> = (0..c.args.len()).map(|j| format!("?a{j}")).collect();
            let b: Vec<String> = (0..c.args.len()).map(|j| format!("?b{j}")).collect();
            let term = |xs: &[String]| {
                if xs.is_empty() {
                    s.clone()
                } else {
                    format!("({s} {})", xs.join(" "))
                }
            };
            let prem = |f: &dyn Fn(&str, &str) -> String| -> String {
                a.iter().zip(&b).map(|(x, y)| f(x, y)).collect::<Vec<_>>().join(" ")
            };
            let _ = writeln!(
                w,
                "(rule scope.{s} ({}) (scoped ?d ?n {}))",
                a.iter().map(|x| format!("(scoped ?d ?n {x})")).collect::<Vec<_>>().join(" "),
                term(&a)
            );
            for op in ["shift", "dshift"] {
                let _ = writeln!(
                    w,
                    "(rule {op}.{s} ({}) ({op} {} ?k {}))",
                    prem(&|x, y| format!("({op} {x} ?k {y})")),
                    term(&a),
                    term(&b)
                );
            }
            for op in ["subst", "dsubst"] {
                let _ = writeln!(
                    w,
                    "(rule {op}.{s} ({}) ({op} {} ?k ?r {}))",
                    prem(&|x, y| format!("({op} {x} ?k ?r {y})")),
                    term(&a),
                    term(&b)
                );
            }
        }
        let shifted_methods = |op: &str, extra: &str| -> String {
            (0..k)
                .map(|i| format!("({op} ?m{i} ?k{extra} ?n{i})"))
                .collect::<Vec<_>>()
                .join(" ")
        };
        let new_methods: String = (0..k).map(|i| format!(" ?n{i}")).collect();
        let _ = writeln!(w, "(rule scope.{e} ((scoped ?d (s ?n) ?p) {} (scoped ?d ?n ?x)) (scoped ?d ?n ({e} ?p {ms} ?x)))",
            methods.iter().map(|m| format!("(scoped ?d ?n {m})")).collect::<Vec<_>>().join(" "));
        let _ = writeln!(w, "(rule shift.{e} ((shift ?p (s ?k) ?p2) {} (shift ?x ?k ?x2)) (shift ({e} ?p {ms} ?x) ?k ({e} ?p2{new_methods} ?x2)))",
            shifted_methods("shift", ""));
        let _ = writeln!(w, "(rule subst.{e} ((shift ?r z ?r2) (subst ?p (s ?k) ?r2 ?p2) {} (subst ?x ?k ?r ?x2)) (subst ({e} ?p {ms} ?x) ?k ?r ({e} ?p2{new_methods} ?x2)))",
            shifted_methods("subst", " ?r"));
        let _ = writeln!(w, "(rule dshift.{e} ((dshift ?p ?k ?p2) {} (dshift ?x ?k ?x2)) (dshift ({e} ?p {ms} ?x) ?k ({e} ?p2{new_methods} ?x2)))",
            shifted_methods("dshift", ""));
        let _ = writeln!(w, "(rule dsubst.{e} ((dsubst ?p ?k ?r ?p2) {} (dsubst ?x ?k ?r ?x2)) (dsubst ({e} ?p {ms} ?x) ?k ?r ({e} ?p2{new_methods} ?x2)))",
            shifted_methods("dsubst", " ?r"));
        // Typing.
        let _ = writeln!(w, "(rule rhas.{t} ((rctx ?d ?g ?phi)) (rhas ?d ?g ?phi {t} (u z)))");
        for c in &self.ctors {
            let s = &c.symbol;
            let a: Vec<String> = (0..c.args.len()).map(|j| format!("?a{j}")).collect();
            let term = if a.is_empty() { s.clone() } else { format!("({s} {})", a.join(" ")) };
            let prems: String = a
                .iter()
                .zip(&c.args)
                .map(|(x, ty)| format!(" (rhas ?d ?g ?phi {x} {ty})"))
                .collect();
            let _ = writeln!(w, "(rule rhas.{s} ((rctx ?d ?g ?phi){prems}) (rhas ?d ?g ?phi {term} {t}))");
            if !a.is_empty() {
                let b: Vec<String> = (0..c.args.len()).map(|j| format!("?b{j}")).collect();
                let prems: String = a
                    .iter()
                    .zip(&b)
                    .zip(&c.args)
                    .map(|((x, y), ty)| format!(" (req ?d ?g ?phi {x} {y} {ty})"))
                    .collect();
                let _ = writeln!(
                    w,
                    "(rule req.{s}-cong ({}) (req ?d ?g ?phi {term} ({s} {}) {t}))",
                    prems.trim_start(),
                    b.join(" ")
                );
            }
        }
        // Eliminator typing: every method type is spelled out with certified
        // shifts and substitutions, as for natrec.
        let mut prems = format!("(rhas ?d (cons {t} ?g) ?phi ?p (u ?l))");
        for (i, c) in self.ctors.iter().enumerate() {
            let (ihs, depth, codomain_args) = self.method_plan(i);
            let chain = |label: String, shifts: usize, prems: &mut String| -> String {
                let mut cur = "?p".to_owned();
                for step in 0..shifts {
                    let next = format!("?p{label}s{step}");
                    let _ = write!(prems, " (shift {cur} (s z) {next})");
                    cur = next;
                }
                cur
            };
            let mut ih_types = Vec::new();
            for (q, &(shifts, var)) in ihs.iter().enumerate() {
                let base = chain(format!("{i}i{q}"), shifts, &mut prems);
                let out = format!("?ih{i}x{q}");
                let _ = write!(prems, " (subst {base} z (v {}) {out})", unary(var));
                ih_types.push(out);
            }
            let base = chain(format!("{i}c"), depth, &mut prems);
            let applied = if c.args.is_empty() {
                c.symbol.clone()
            } else {
                format!(
                    "({} {})",
                    c.symbol,
                    codomain_args.iter().map(|&v| format!("(v {})", unary(v))).collect::<Vec<_>>().join(" ")
                )
            };
            let cod = format!("?cod{i}");
            let _ = write!(prems, " (subst {base} z {applied} {cod})");
            let mut method_ty = cod;
            for ih in ih_types.iter().rev() {
                method_ty = format!("(pi {ih} {method_ty})");
            }
            for ty in c.args.iter().rev() {
                method_ty = format!("(pi {ty} {method_ty})");
            }
            let _ = write!(prems, " (rhas ?d ?g ?phi ?m{i} {method_ty})");
        }
        let _ = write!(prems, " (rhas ?d ?g ?phi ?x {t}) (subst ?p z ?x ?px) (rhas ?d ?g ?phi ?px (u ?l))");
        let _ = writeln!(w, "(rule rhas.{e} ({prems}) (rhas ?d ?g ?phi ({e} ?p {ms} ?x) ?px))");
        // Computation, congruence, composition.
        for (i, c) in self.ctors.iter().enumerate() {
            let a: Vec<String> = (0..c.args.len()).map(|j| format!("?a{j}")).collect();
            let scrutinee = if a.is_empty() { c.symbol.clone() } else { format!("({} {})", c.symbol, a.join(" ")) };
            let mut rhs = format!("?m{i}");
            for x in &a {
                rhs = format!("(app {rhs} {x})");
            }
            for &j in &c.recursive {
                rhs = format!("(app {rhs} ({e} ?p {ms} ?a{j}))");
            }
            let lhs = format!("({e} ?p {ms} {scrutinee})");
            let _ = writeln!(
                w,
                "(rule req.{e}.{} ((rhas ?d ?g ?phi {lhs} ?ty) (rhas ?d ?g ?phi {rhs} ?ty)) (req ?d ?g ?phi {lhs} {rhs} ?ty))",
                c.symbol
            );
        }
        let _ = writeln!(w, "(rule req.{e}-cong ((rhas ?d ?g ?phi ({e} ?p {ms} ?x) ?ty) (rhas ?d ?g ?phi ({e} ?p {ms} ?x2) ?ty) (req ?d ?g ?phi ?x ?x2 {t})) (req ?d ?g ?phi ({e} ?p {ms} ?x) ({e} ?p {ms} ?x2) ?ty))");
        let _ = writeln!(w, "(rule req.comp-{t} ((rhas ?d ?g ?psi (comp {t} ?phi ?t ?b) {t})) (req ?d ?g ?psi (comp {t} ?phi ?t ?b) ?b {t}))");
        out
    }
}

/// The core term of a declared type, constructor application or eliminator.
pub fn type_term(data: &Data) -> Sexp {
    atom(&data.ty)
}
pub fn ctor_term(c: &Ctor, args: Vec<Sexp>) -> Sexp {
    if args.is_empty() {
        atom(&c.symbol)
    } else {
        call(&c.symbol, args)
    }
}
