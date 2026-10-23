//! User-declared data types, possibly with type parameters. A declaration
//! generates an explicit theory fragment (formation, constructors, a
//! dependent eliminator, computation, congruence, structure and
//! composition) that is appended to the selected theory and shipped with
//! every certificate that uses it; nothing is built in.
//!
//! The typing rules are produced from premise plans (`Plan`). The same plan
//! is printed as rule text and interpreted by the engine when it infers a
//! type, so the emitted steps state the rule's premises in its order by
//! construction.
//!
//! Field types are bool, nat, earlier closed data types, a parameter, or the
//! type itself at the same parameters. Without function or universe fields,
//! strict positivity is immediate. Composition:
//! - a closed type (no parameters) has only discrete fields, so it is
//!   discrete (a constant presheaf in the cubical-set model) and composition
//!   returns its base;
//! - a parameterized type gets transport rules (empty face) that compute
//!   constructorwise, `transp (T A) (c a…) = c (transp A a)…`, which holds in
//!   the standard models of inductive families. Other compositions in a
//!   parameterized type are left without a rule.
//!
//! - a type with a path constructor (a higher inductive type) is not
//!   discrete: a homogeneous composition in it is a formal point, and the
//!   eliminator commutes with it along the filler (CHM 2018). With
//!   parameters, it also transports constructorwise; a path constructor
//!   keeps its interval, which agrees with its boundary because endpoints
//!   are built from constructors and fields.
//!
//! A path constructor has closed discrete fields and recursive fields; its
//! endpoints are point constructors applied to its fields and closed terms,
//! or a recursive field itself (as in a propositional truncation). Its terms
//! take an interval after the fields, and its eliminator method takes an
//! induction hypothesis for every recursive field, like a point
//! constructor's.
//!
//! Constructor terms do not carry the parameters: they are read off the
//! fields or the expected type, as for unannotated lambdas.
use super::path_frontend::v;
use super::term::{Sexp, atom, call};
use std::cell::RefCell;
use std::fmt::Write;
use std::rc::Rc;

#[derive(Clone)]
pub enum ArgTy {
    /// A closed discrete type: bool, nat or an earlier closed data type.
    Closed(Sexp),
    /// The parameter with this index.
    Param(usize),
    /// The declared type at its own parameters.
    Rec,
}

/// A path constructor's endpoint, over the constructor's fields.
#[derive(Clone)]
pub enum End {
    /// The field with this index.
    Field(usize),
    /// A point constructor of the type, by index, applied to endpoints.
    Ctor(usize, Vec<End>),
    /// A closed term, at a field of a closed type.
    Closed(Sexp),
}

impl End {
    /// The endpoint as a template, with `field` for each field.
    pub fn tpl(&self, data: &Data, field: &dyn Fn(usize) -> Tpl) -> Tpl {
        match self {
            End::Field(k) => field(*k),
            End::Ctor(i, args) => Tpl::app(
                &data.ctors[*i].symbol,
                args.iter().map(|a| a.tpl(data, field)).collect(),
            ),
            End::Closed(s) => Tpl::Ground(s.clone()),
        }
    }
    /// The endpoint at actual fields.
    pub fn at(&self, data: &Data, fields: &[Sexp]) -> Sexp {
        let t = self.tpl(data, &|k| Tpl::Ground(fields[k].clone()));
        ground(&t)
    }
    /// The point constructors it uses, by index.
    fn ctors(&self, out: &mut Vec<usize>) {
        if let End::Ctor(i, args) = self {
            if !out.contains(i) {
                out.push(*i);
            }
            for a in args {
                a.ctors(out);
            }
        }
    }
}

fn ground(t: &Tpl) -> Sexp {
    match t {
        Tpl::Var(v) => panic!("template variable {v} in a ground term"),
        Tpl::Ground(s) => s.clone(),
        Tpl::App(h, xs) => call(h, xs.iter().map(ground).collect::<Vec<_>>()),
    }
}

pub struct Ctor {
    pub name: String,
    pub symbol: String,
    pub args: Vec<ArgTy>,
    /// A path constructor's endpoints, point terms of the type over its
    /// fields. Its terms take one interval argument after the fields.
    pub boundary: Option<(End, End)>,
}

impl Ctor {
    /// The number of arguments its terms take: fields, then an interval for
    /// a path constructor.
    pub fn arity(&self) -> usize {
        self.args.len() + usize::from(self.boundary.is_some())
    }
    pub fn recursive(&self) -> Vec<usize> {
        (0..self.args.len())
            .filter(|&k| matches!(self.args[k], ArgTy::Rec))
            .collect()
    }
}

pub struct Data {
    pub name: String,
    pub ty: String,
    pub elim: String,
    pub params: usize,
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
/// Whether a constructor term's type follows from its fields: every
/// parameter is the type of one of them, or a recursive field's type
/// follows from its own.
pub fn determined(t: &Sexp) -> bool {
    let (head, fields): (&str, &[Sexp]) = match t {
        Sexp::Atom(a) => (a, &[]),
        Sexp::List(xs) => (
            xs.first().and_then(|h| h.atom().ok()).unwrap_or(""),
            &xs[1..],
        ),
    };
    let Some((data, i)) = by_ctor(head) else {
        return true;
    };
    let args = &data.ctors[i].args;
    (0..data.params).all(|j| args.iter().any(|a| matches!(a, ArgTy::Param(k) if *k == j)))
        || args
            .iter()
            .zip(fields)
            .any(|(a, f)| matches!(a, ArgTy::Rec) && determined(f))
}
/// The argument position of a path constructor's interval.
pub fn interval_index(symbol: &str) -> Option<usize> {
    let (data, i) = by_ctor(symbol)?;
    let c = &data.ctors[i];
    c.boundary.as_ref().map(|_| c.args.len())
}
/// The argument position of an eliminator's motive, which binds one variable.
pub fn motive_index(symbol: &str) -> Option<usize> {
    by_elim(symbol).map(|d| d.params)
}

/// `head` applied to `args`, or the atom when there are none.
pub fn apply(head: &str, args: Vec<Sexp>) -> Sexp {
    if args.is_empty() {
        atom(head)
    } else {
        call(head, args)
    }
}

/// A rule template: `?`-variables, ground terms and applications.
#[derive(Clone)]
pub enum Tpl {
    Var(String),
    Ground(Sexp),
    App(String, Vec<Tpl>),
}

impl Tpl {
    fn app(head: &str, args: Vec<Tpl>) -> Tpl {
        if args.is_empty() {
            Tpl::Ground(atom(head))
        } else {
            Tpl::App(head.to_owned(), args)
        }
    }
    pub fn text(&self) -> String {
        match self {
            Tpl::Var(v) => format!("?{v}"),
            Tpl::Ground(s) => s.to_string(),
            Tpl::App(h, xs) => {
                let xs: Vec<_> = xs.iter().map(Tpl::text).collect();
                format!("({h} {})", xs.join(" "))
            }
        }
    }
}

/// One premise of a typing rule, in order.
pub enum Prem {
    /// `(rctx ?d ?g ?phi)`
    Ctx,
    /// `(rhas ?d Γ ?phi term ty)`, with Γ = `(cons ext ?g)` when extended.
    Has {
        ext: Option<Tpl>,
        term: Tpl,
        ty: Tpl,
    },
    /// `(shift from cutoff to)`, cutoff 0 or 1.
    Shift {
        from: Tpl,
        cutoff: usize,
        to: String,
    },
    /// `(dshift from z to)`: room for one dimension.
    DShift { from: String, to: String },
    /// `(interval ?d ?i)`
    Interval(String),
    /// `(subst from z by to)`
    Subst { from: String, by: Tpl, to: String },
}

pub struct Plan {
    pub prems: Vec<Prem>,
    pub term: Tpl,
    pub ty: Tpl,
    fresh: usize,
}

impl Plan {
    fn new() -> Self {
        Plan {
            prems: Vec::new(),
            term: Tpl::Var(String::new()),
            ty: Tpl::Var(String::new()),
            fresh: 0,
        }
    }
    fn var(&mut self) -> String {
        self.fresh += 1;
        format!("t{}", self.fresh)
    }
    /// Shift `from` `times` times at `cutoff`; the name of the result.
    fn chain(&mut self, from: &str, cutoff: usize, times: usize) -> String {
        self.chain_tpl(var(from.to_owned()), cutoff, times)
    }
    /// Shift a template `times` times at `cutoff`. A template that is not a
    /// variable is only named by a shift, so it needs `times > 0`.
    fn chain_tpl(&mut self, from: Tpl, cutoff: usize, times: usize) -> String {
        let mut cur = from;
        for _ in 0..times {
            let to = self.var();
            self.prems.push(Prem::Shift {
                from: cur,
                cutoff,
                to: to.clone(),
            });
            cur = var(to);
        }
        match cur {
            Tpl::Var(v) => v,
            _ => panic!("chain_tpl names a template only by shifting it"),
        }
    }
    fn has(&mut self, term: Tpl, ty: Tpl) {
        self.prems.push(Prem::Has {
            ext: None,
            term,
            ty,
        });
    }
    pub fn text(&self, name: &str) -> String {
        let prems: Vec<String> = self
            .prems
            .iter()
            .map(|p| match p {
                Prem::Ctx => "(rctx ?d ?g ?phi)".to_owned(),
                Prem::Has { ext, term, ty } => {
                    let g = match ext {
                        Some(e) => format!("(cons {} ?g)", e.text()),
                        None => "?g".to_owned(),
                    };
                    format!("(rhas ?d {g} ?phi {} {})", term.text(), ty.text())
                }
                Prem::Shift { from, cutoff, to } => {
                    let c = if *cutoff == 0 { "z" } else { "(s z)" };
                    format!("(shift {} {c} ?{to})", from.text())
                }
                Prem::DShift { from, to } => format!("(dshift ?{from} z ?{to})"),
                Prem::Interval(i) => format!("(interval ?d ?{i})"),
                Prem::Subst { from, by, to } => format!("(subst ?{from} z {} ?{to})", by.text()),
            })
            .collect();
        format!(
            "(rule {name} ({}) (rhas ?d ?g ?phi {} {}))\n",
            prems.join(" "),
            self.term.text(),
            self.ty.text()
        )
    }
}

fn var(name: String) -> Tpl {
    Tpl::Var(name)
}

impl Data {
    /// The eliminator's value on an endpoint, by its computation rules:
    /// `c a… ↦ m a… (elim … r)…` for the recursive fields `r`, and a
    /// recursive field of the path constructor is its induction hypothesis.
    /// `field` and `ih` name the path constructor's fields and hypotheses.
    fn unfold(
        &self,
        e: &End,
        methods: &[Tpl],
        field: &dyn Fn(usize) -> Tpl,
        ih: &dyn Fn(usize) -> Tpl,
    ) -> Tpl {
        match e {
            End::Field(k) => ih(*k),
            End::Ctor(i, args) => {
                let mut out = methods[*i].clone();
                for a in args {
                    out = Tpl::App("app".into(), vec![out, a.tpl(self, field)]);
                }
                for j in self.ctors[*i].recursive() {
                    let h = self.unfold(&args[j], methods, field, ih);
                    out = Tpl::App("app".into(), vec![out, h]);
                }
                out
            }
            End::Closed(_) => panic!("a closed endpoint is not of the declared type"),
        }
    }
    /// Whether the type has a path constructor.
    pub fn is_higher(&self) -> bool {
        self.ctors.iter().any(|c| c.boundary.is_some())
    }
    fn params_tpl(&self) -> Vec<Tpl> {
        (0..self.params).map(|j| var(format!("A{j}"))).collect()
    }
    fn type_tpl(&self, params: Vec<Tpl>) -> Tpl {
        Tpl::app(&self.ty, params)
    }
    fn field_ty(&self, a: &ArgTy, params: &[Tpl]) -> Tpl {
        match a {
            ArgTy::Closed(s) => Tpl::Ground(s.clone()),
            ArgTy::Param(j) => params[*j].clone(),
            ArgTy::Rec => self.type_tpl(params.to_vec()),
        }
    }
    /// The type of a field as a ground term, given the actual parameters.
    pub fn field_type(&self, a: &ArgTy, params: &[Sexp]) -> Sexp {
        match a {
            ArgTy::Closed(s) => s.clone(),
            ArgTy::Param(j) => params[*j].clone(),
            ArgTy::Rec => apply(&self.ty, params.to_vec()),
        }
    }

    pub fn formation_plan(&self) -> Plan {
        let mut p = Plan::new();
        p.prems.push(Prem::Ctx);
        for a in self.params_tpl() {
            p.has(a, Tpl::Ground(call("u", [atom("z")])));
        }
        p.term = self.type_tpl(self.params_tpl());
        p.ty = Tpl::Ground(call("u", [atom("z")]));
        p
    }

    pub fn ctor_plan(&self, i: usize) -> Plan {
        let c = &self.ctors[i];
        let params = self.params_tpl();
        let mut p = Plan::new();
        p.prems.push(Prem::Ctx);
        for a in &params {
            p.has(a.clone(), Tpl::Ground(call("u", [atom("z")])));
        }
        let fields: Vec<Tpl> = (0..c.args.len()).map(|k| var(format!("a{k}"))).collect();
        for (f, a) in fields.iter().zip(&c.args) {
            let ty = self.field_ty(a, &params);
            p.has(f.clone(), ty);
        }
        let mut args = fields;
        if c.boundary.is_some() {
            p.prems.push(Prem::Interval("i".into()));
            args.push(var("i".into()));
        }
        p.term = Tpl::app(&c.symbol, args);
        p.ty = self.type_tpl(params);
        p
    }

    /// The eliminator's typing. Method types are spelled out with shifts and
    /// substitutions: a field type sits under the earlier fields' binders; an
    /// induction hypothesis and the codomain instantiate the motive, which
    /// lives over `(x, Γ)`, after shifting at cutoff 1 to make room.
    pub fn elim_plan(&self) -> Plan {
        let params = self.params_tpl();
        let level = Tpl::App("u".into(), vec![var("l".into())]);
        let u0 = Tpl::Ground(call("u", [atom("z")]));
        let mut p = Plan::new();
        for a in &params {
            p.has(a.clone(), u0.clone());
        }
        p.prems.push(Prem::Has {
            ext: Some(self.type_tpl(params.clone())),
            term: var("p".into()),
            ty: level.clone(),
        });
        let shifted = |p: &mut Plan, times: usize| -> Vec<Tpl> {
            (0..self.params)
                .map(|j| var(p.chain(&format!("A{j}"), 0, times)))
                .collect()
        };
        let methods: Vec<Tpl> = (0..self.ctors.len())
            .map(|i| var(format!("m{i}")))
            .collect();
        for (i, c) in self.ctors.iter().enumerate() {
            let (n, rec) = (c.args.len(), c.recursive());
            let r = rec.len();
            let mut domains = Vec::new();
            for (k, a) in c.args.iter().enumerate() {
                let here = shifted(&mut p, k);
                domains.push(self.field_ty(a, &here));
            }
            let mut ihs = Vec::new();
            for (q, &j) in rec.iter().enumerate() {
                let base = p.chain("p", 1, n + q);
                let to = p.var();
                p.prems.push(Prem::Subst {
                    from: base,
                    by: Tpl::Ground(v(n - 1 - j + q)),
                    to: to.clone(),
                });
                ihs.push(var(to));
            }
            // Under the fields and hypotheses: field k, and the hypothesis
            // of recursive field k.
            let field = |k: usize| Tpl::Ground(v(n - 1 - k + r));
            let ih = |k: usize| {
                let q = rec.iter().position(|&j| j == k).expect("a recursive field");
                Tpl::Ground(v(r - 1 - q))
            };
            let fields: Vec<Tpl> = (0..n).map(field).collect();
            let mut ty = if let Some((left, right)) = &c.boundary {
                // PathP (i. P (c fields i)) (elim … left) (elim … right): the
                // motive under the fields and hypotheses, then under one
                // dimension.
                let base = p.chain("p", 1, n + r);
                let lifted = p.var();
                p.prems.push(Prem::DShift {
                    from: base,
                    to: lifted.clone(),
                });
                let mut point = fields;
                point.push(Tpl::Ground(call("dim", [atom("z")])));
                let fam = p.var();
                p.prems.push(Prem::Subst {
                    from: lifted,
                    by: Tpl::app(&c.symbol, point),
                    to: fam.clone(),
                });
                // The endpoints are what the eliminator computes on them,
                // spelled out with the methods: stating them with the
                // eliminator itself would make its typing rule circular.
                let mut used = Vec::new();
                left.ctors(&mut used);
                right.ctors(&mut used);
                let mut here = methods.clone();
                for j in used {
                    here[j] = var(p.chain(&format!("m{j}"), 0, n + r));
                }
                let e0 = self.unfold(left, &here, &field, &ih);
                let e1 = self.unfold(right, &here, &field, &ih);
                Tpl::App("path".into(), vec![var(fam), e0, e1])
            } else {
                let base = p.chain("p", 1, n + r);
                let applied = Tpl::app(&c.symbol, fields);
                let cod = p.var();
                p.prems.push(Prem::Subst {
                    from: base,
                    by: applied,
                    to: cod.clone(),
                });
                var(cod)
            };
            for ih in ihs.into_iter().rev() {
                ty = Tpl::App("pi".into(), vec![ih, ty]);
            }
            for dom in domains.into_iter().rev() {
                ty = Tpl::App("pi".into(), vec![dom, ty]);
            }
            p.has(var(format!("m{i}")), ty);
        }
        p.has(var("x".into()), self.type_tpl(params.clone()));
        p.prems.push(Prem::Subst {
            from: "p".into(),
            by: var("x".into()),
            to: "px".into(),
        });
        p.has(var("px".into()), level);
        let mut args = params;
        args.push(var("p".into()));
        args.extend((0..self.ctors.len()).map(|i| var(format!("m{i}"))));
        args.push(var("x".into()));
        p.term = Tpl::App(self.elim.clone(), args);
        p.ty = var("px".into());
        p
    }

    /// The generated theory fragment.
    pub fn theory(&self) -> String {
        let (t, e, np) = (&self.ty, &self.elim, self.params);
        let mut out = String::new();
        let w = &mut out;
        let k = self.ctors.len();
        let _ = writeln!(w, "; data {} (generated)", self.name);
        let tm = |n: usize| vec!["Tm"; n].join(" ");
        let _ = writeln!(w, "(ctor {t} ({}) Tm)", tm(np));
        for c in &self.ctors {
            let sorts = if c.boundary.is_some() {
                format!("{} I", tm(c.args.len())).trim().to_owned()
            } else {
                tm(c.args.len())
            };
            let _ = writeln!(w, "(ctor {} ({sorts}) Tm)", c.symbol);
        }
        let _ = writeln!(w, "(ctor {e} ({}) Tm)", tm(np + k + 2));
        // Structure: argumentwise, except the eliminator's motive binder.
        // A path constructor's interval argument is scoped as an interval,
        // kept by ordinary operations and mapped by dimension operations.
        let structural = |w: &mut String,
                          head: &str,
                          arity: usize,
                          binder: Option<usize>,
                          interval: Option<usize>| {
            let xs: Vec<String> = (0..arity).map(|i| format!("?x{i}")).collect();
            let ys: Vec<String> = (0..arity).map(|i| format!("?y{i}")).collect();
            let term = |zs: &[String]| {
                if zs.is_empty() {
                    head.to_owned()
                } else {
                    format!("({head} {})", zs.join(" "))
                }
            };
            let scope: Vec<String> = (0..arity)
                .map(|i| {
                    if Some(i) == interval {
                        return format!("(interval ?d ?x{i})");
                    }
                    let n = if Some(i) == binder { "(s ?n)" } else { "?n" };
                    format!("(scoped ?d {n} ?x{i})")
                })
                .collect();
            let _ = writeln!(
                w,
                "(rule scope.{head} ({}) (scoped ?d ?n {}))",
                scope.join(" "),
                term(&xs)
            );
            for op in ["shift", "subst", "dshift", "dsubst"] {
                let r = if op.ends_with("subst") { " ?r" } else { "" };
                let mut prems = Vec::new();
                let mut ys = ys.clone();
                for i in 0..arity {
                    let ordinary = !op.starts_with('d') && Some(i) == binder;
                    if Some(i) == interval {
                        match op {
                            "dshift" => prems.push(format!("(ishift ?x{i} ?k ?y{i})")),
                            "dsubst" => prems.push(format!("(isubst ?x{i} ?k ?r ?y{i})")),
                            _ => ys[i] = format!("?x{i}"),
                        }
                    } else if ordinary && op == "subst" {
                        prems.push("(shift ?r z ?r2)".to_owned());
                        prems.push(format!("(subst ?x{i} (s ?k) ?r2 ?y{i})"));
                    } else if ordinary {
                        prems.push(format!("(shift ?x{i} (s ?k) ?y{i})"));
                    } else {
                        prems.push(format!("({op} ?x{i} ?k{r} ?y{i})"));
                    }
                }
                let _ = writeln!(
                    w,
                    "(rule {op}.{head} ({}) ({op} {} ?k{r} {}))",
                    prems.join(" "),
                    term(&xs),
                    term(&ys)
                );
            }
        };
        structural(w, t, np, None, None);
        for c in &self.ctors {
            let interval = c.boundary.as_ref().map(|_| c.args.len());
            structural(w, &c.symbol, c.arity(), None, interval);
        }
        structural(w, e, np + k + 2, Some(np), None);
        // Typing, from the shared plans.
        w.push_str(&self.formation_plan().text(&format!("rhas.{t}")));
        for (i, c) in self.ctors.iter().enumerate() {
            w.push_str(&self.ctor_plan(i).text(&format!("rhas.{}", c.symbol)));
        }
        w.push_str(&self.elim_plan().text(&format!("rhas.{e}")));
        let params: Vec<String> = (0..np).map(|j| format!("?A{j}")).collect();
        let params_tpl = self.params_tpl();
        let ty_text = self.type_tpl(params_tpl.clone()).text();
        let methods: Vec<String> = (0..k).map(|i| format!("?m{i}")).collect();
        let head_args = |extra: &str| -> String {
            let mut xs = params.clone();
            xs.push("?p".into());
            xs.extend(methods.iter().cloned());
            xs.push(extra.to_owned());
            format!("({e} {})", xs.join(" "))
        };
        // Type congruence (parameters as types), then constructor congruence.
        let params2: Vec<String> = (0..np).map(|j| format!("?C{j}")).collect();
        if np > 0 {
            let prems: Vec<String> = params
                .iter()
                .zip(&params2)
                .map(|(x, y)| format!("(req ?d ?g ?phi {x} {y} (u z))"))
                .collect();
            let _ = writeln!(
                w,
                "(rule req.{t}-cong ({}) (req ?d ?g ?phi ({t} {}) ({t} {}) (u z)))",
                prems.join(" "),
                params.join(" "),
                params2.join(" ")
            );
        }
        for c in &self.ctors {
            if c.args.is_empty() || c.boundary.is_some() {
                continue;
            }
            let a: Vec<String> = (0..c.args.len()).map(|j| format!("?a{j}")).collect();
            let b: Vec<String> = (0..c.args.len()).map(|j| format!("?b{j}")).collect();
            let prems: Vec<String> = a
                .iter()
                .zip(&b)
                .zip(&c.args)
                .map(|((x, y), ty)| {
                    format!(
                        "(req ?d ?g ?phi {x} {y} {})",
                        self.field_ty(ty, &params_tpl).text()
                    )
                })
                .collect();
            let lhs = format!("({} {})", c.symbol, a.join(" "));
            let rhs = format!("({} {})", c.symbol, b.join(" "));
            let _ = writeln!(
                w,
                "(rule req.{}-cong ({}) (req ?d ?g ?phi {lhs} {rhs} {ty_text}))",
                c.symbol,
                prems.join(" ")
            );
        }
        // Path constructors: boundary, congruence and computation.
        for (i, c) in self.ctors.iter().enumerate() {
            let Some((left, right)) = &c.boundary else {
                continue;
            };
            let a: Vec<String> = (0..c.args.len()).map(|j| format!("?a{j}")).collect();
            let b: Vec<String> = (0..c.args.len()).map(|j| format!("?b{j}")).collect();
            let at = |xs: &[String], i: &str| {
                let mut xs = xs.to_vec();
                xs.push(i.to_owned());
                format!("({} {})", c.symbol, xs.join(" "))
            };
            let point = at(&a, "?i");
            for (end, value) in [("0", left), ("1", right)] {
                let value = value.tpl(self, &|k| var(format!("a{k}"))).text();
                let _ = writeln!(
                    w,
                    "(rule req.{}-{end} ((rhas ?d ?g ?phi {point} {ty_text}) (local ?d ?phi ?i i{end}) (rhas ?d ?g ?phi {value} {ty_text})) (req ?d ?g ?phi {point} {value} {ty_text}))",
                    c.symbol
                );
            }
            let mut prems: Vec<String> = a
                .iter()
                .zip(&b)
                .zip(&c.args)
                .map(|((x, y), ty)| {
                    format!(
                        "(req ?d ?g ?phi {x} {y} {})",
                        self.field_ty(ty, &params_tpl).text()
                    )
                })
                .collect();
            prems.push(format!("(rhas ?d ?g ?phi {point} {ty_text})"));
            prems.push("(local ?d ?phi ?i ?j)".into());
            prems.push("(interval ?d ?j)".into());
            let _ = writeln!(
                w,
                "(rule req.{}-cong ({}) (req ?d ?g ?phi {point} {} {ty_text}))",
                c.symbol,
                prems.join(" "),
                at(&b, "?j")
            );
            let mut rhs = format!("?m{i}");
            for x in &a {
                rhs = format!("(app {rhs} {x})");
            }
            for j in c.recursive() {
                rhs = format!("(app {rhs} {})", head_args(&format!("?a{j}")));
            }
            let rhs = format!("(papp {rhs} ?i)");
            let lhs = head_args(&point);
            let _ = writeln!(
                w,
                "(rule req.{e}.{} ((rhas ?d ?g ?phi {lhs} ?ty) (rhas ?d ?g ?phi {rhs} ?ty)) (req ?d ?g ?phi {lhs} {rhs} ?ty))",
                c.symbol
            );
        }
        // The eliminator on a formal composition (CHM 2018): composition in
        // the motive along the filler, of the eliminator on tube and base.
        if self.is_higher() {
            // The composition's family is the eliminator's type, weakened by
            // its dimension: a homogeneous composition.
            let weak: Vec<String> = (0..np).map(|j| format!("?B{j}")).collect();
            let family = if np == 0 {
                t.clone()
            } else {
                format!("({t} {})", weak.join(" "))
            };
            let scrutinee = format!("(comp {family} ?phi ?t ?u)");
            let shifted: Vec<String> = (0..k).map(|i| format!("?n{i}")).collect();
            let mut prems = vec![format!("(rhas ?d ?g ?psi {} ?ty)", head_args(&scrutinee))];
            prems.extend((0..np).map(|j| format!("(dshift ?A{j} z ?B{j})")));
            prems.extend([
                format!("(filldef {family} ?phi ?t ?u ?fill)"),
                "(dshift ?p z ?p1)".to_owned(),
                "(subst ?p1 z ?fill ?pf)".to_owned(),
            ]);
            prems.extend((0..k).map(|i| format!("(dshift ?m{i} z ?n{i})")));
            let mut inner = weak.clone();
            inner.push("?p1".into());
            inner.extend(shifted.iter().cloned());
            inner.push("?t".into());
            let tube = format!("({e} {})", inner.join(" "));
            let rhs = format!("(comp ?pf ?phi {tube} {})", head_args("?u"));
            prems.push(format!("(rhas ?d ?g ?psi {rhs} ?ty)"));
            let _ = writeln!(
                w,
                "(rule req.{e}.hcomp ({}) (req ?d ?g ?psi {} {rhs} ?ty))",
                prems.join(" "),
                head_args(&scrutinee)
            );
        }
        // Computation: one rule per point constructor.
        for (i, c) in self.ctors.iter().enumerate() {
            if c.boundary.is_some() {
                continue;
            }
            let a: Vec<String> = (0..c.args.len()).map(|j| format!("?a{j}")).collect();
            let scrutinee = if a.is_empty() {
                c.symbol.clone()
            } else {
                format!("({} {})", c.symbol, a.join(" "))
            };
            let mut rhs = format!("?m{i}");
            for x in &a {
                rhs = format!("(app {rhs} {x})");
            }
            for j in c.recursive() {
                rhs = format!("(app {rhs} {})", head_args(&format!("?a{j}")));
            }
            let lhs = head_args(&scrutinee);
            let _ = writeln!(
                w,
                "(rule req.{e}.{} ((rhas ?d ?g ?phi {lhs} ?ty) (rhas ?d ?g ?phi {rhs} ?ty)) (req ?d ?g ?phi {lhs} {rhs} ?ty))",
                c.symbol
            );
        }
        let _ = writeln!(
            w,
            "(rule req.{e}-cong ((rhas ?d ?g ?phi {} ?ty) (rhas ?d ?g ?phi {} ?ty) (req ?d ?g ?phi ?x ?x2 {ty_text})) (req ?d ?g ?phi {} {} ?ty))",
            head_args("?x"),
            head_args("?x2"),
            head_args("?x"),
            head_args("?x2")
        );
        // Composition. A higher inductive type is not discrete: a
        // composition in it is a formal point, taken apart by the
        // eliminator's hcomp rule above.
        if self.is_higher() && np == 0 {
        } else if np == 0 {
            let _ = writeln!(
                w,
                "(rule req.comp-{t} ((rhas ?d ?g ?psi (comp {t} ?phi ?t ?b) {t})) (req ?d ?g ?psi (comp {t} ?phi ?t ?b) ?b {t}))"
            );
        } else {
            // Transport constructorwise, a path constructor at the same
            // interval: its endpoints are constructors of its fields, so
            // transport commutes with them strictly.
            for c in &self.ctors {
                let a: Vec<String> = (0..c.args.len()).map(|j| format!("?a{j}")).collect();
                let wrap = |xs: &[String]| {
                    let mut xs = xs.to_vec();
                    if c.boundary.is_some() {
                        xs.push("?i".into());
                    }
                    if xs.is_empty() {
                        c.symbol.clone()
                    } else {
                        format!("({} {})", c.symbol, xs.join(" "))
                    }
                };
                let lhs = format!("(comp {ty_text} ff ?t {})", wrap(&a));
                let parts: Vec<String> = a
                    .iter()
                    .zip(&c.args)
                    .map(|(x, ty)| {
                        format!(
                            "(comp {} ff zero {x})",
                            self.field_ty(ty, &params_tpl).text()
                        )
                    })
                    .collect();
                let rhs = wrap(&parts);
                let _ = writeln!(
                    w,
                    "(rule req.comp-{t}.{} ((rhas ?d ?g ?psi {lhs} ?out) (rhas ?d ?g ?psi {rhs} ?out)) (req ?d ?g ?psi {lhs} {rhs} ?out))",
                    c.symbol
                );
            }
        }
        out
    }
}
