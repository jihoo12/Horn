//! Cubical scripts: definitions, typing checks and evaluation, elaborated to
//! the core syntax and certified by the engine. Every `def`, `check` and
//! `eval` becomes a fixed goal; the whole derivation is encoded as an oracle
//! and checked by the kernel before any result is reported.
//!
//! ```text
//! (def not (pi b bool bool) (lam b bool (bif c bool bfalse btrue b)))
//! (eval r (app not btrue))                       ; r = bfalse : bool
//! ```
//!
//! `(data NAME (CTOR ARG-TYPE...) ...)` declares a closed data type; its
//! rules are generated and appended to the theory the certificate is checked
//! against. Constructors apply like functions, `(elim NAME k P (METHODS...) x)`
//! eliminates into the motive P over `k : NAME`.
//!
//! Terms use named binders. `(lam x A body)`, `(pi x A B)`, `(sigma x A B)`,
//! `(plam i body)`, `(path i A l r)` or `(path A l r)`, `(papp p r)`,
//! `(bif c P t f b)` (P is the motive over `c : bool`), `(suc n)`,
//! `(natrec k P z s n)` (motive P over `k : nat`, `s : Π k. P k → P (suc k)`),
//! numerals, `(pair a b)`,
//! `(fst p)`, `(snd p)`, `(app f a ...)`, `(ann t A)`, `(u N)`, `(equiv A B)`
//! and `(transport i A x)` (transport of x along the line `i ↦ A`).
//! Constants are `bool btrue bfalse nat zero`. The prelude names `ua`
//! (`Π A B : U0. Equiv A B → Path U0 A B`) and `iso-equiv`
//! (`Π X Y f g s t. isEquiv f`) are closed library terms, checked like any
//! definition; neither is an axiom. Definitions are closed and transparent.
use super::engine::data::{self, ArgTy, Ctor, Data};
use super::engine::face_frontend::Face;
use super::engine::iso_equiv_frontend::{iso_equiv_term, iso_equiv_type};
use super::engine::path_frontend::{dim, papp, path, u, v};
use super::engine::restricted_frontend::RestrictedProducer;
use super::engine::ua_frontend::{ua_term, ua_type};
use super::generate::{Regenerated, certify};
use super::engine::term::{Result, Sexp, atom, call, parse};
use std::collections::HashMap;

const FUEL: usize = 100_000;

/// One reported evaluation: `name = value : type`.
pub struct Evaluation {
    pub name: String,
    pub value: String,
    pub ty: String,
}

pub struct Script {
    pub certified: Regenerated,
    pub evaluations: Vec<Evaluation>,
}

#[derive(Clone, Default)]
struct Names {
    ordinary: Vec<String>,
    dimensions: Vec<String>,
}

impl Names {
    fn with_ordinary(&self, name: &str) -> Self {
        let mut out = self.clone();
        out.ordinary.push(name.to_owned());
        out
    }
    fn with_dimension(&self, name: &str) -> Self {
        let mut out = self.clone();
        out.dimensions.push(name.to_owned());
        out
    }
}

fn index(names: &[String], name: &str) -> Option<usize> {
    names.iter().rev().position(|n| n == name)
}

fn level(s: &Sexp) -> Result<usize> {
    let text = s.atom()?;
    match text.parse::<usize>() {
        Ok(n) if n <= 8 && text.bytes().all(|c| c.is_ascii_digit()) => Ok(n),
        _ => Err(format!("expected a universe level 0..8, found {text}")),
    }
}

fn binder(s: &Sexp) -> Result<&str> {
    let name = s.atom()?;
    let ok = name
        .chars()
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '\''));
    if !ok || RESERVED.contains(&name) {
        return Err(format!("invalid binder name {name}"));
    }
    Ok(name)
}

const RESERVED: &[&str] = &[
    "bool", "btrue", "bfalse", "nat", "zero", "i0", "i1", "u", "pi", "lam", "app", "sigma",
    "pair", "fst", "snd", "path", "plam", "papp", "bif", "ann", "equiv", "transport", "neg",
    "meet", "join", "ua", "iso-equiv", "suc", "natrec", "data", "elim",
];

struct Elaborator {
    p: RestrictedProducer,
    defs: HashMap<String, Sexp>,
    prelude: HashMap<&'static str, Sexp>,
}

impl Elaborator {
    fn new() -> Result<Self> {
        let mut p = RestrictedProducer::default();
        p.f.path.p.archive_judgments();
        p.reuse_restricted_typings();
        p.f.path.memoize_transformations();
        p.reuse_certified_checks();
        p.strengthen_typings();
        p.keep_reduct_types();
        p.enable_composition_computation();
        let mut prelude = HashMap::new();
        prelude.insert("ua", call("ann", [ua_term(), ua_type(&mut p, 0)?]));
        prelude.insert(
            "iso-equiv",
            call(
                "ann",
                [iso_equiv_term(&mut p, 0, 0)?, iso_equiv_type(&mut p, 0, 0)?],
            ),
        );
        Ok(Self {
            p,
            defs: HashMap::new(),
            prelude,
        })
    }

    fn interval(&self, s: &Sexp, names: &Names) -> Result<Sexp> {
        match s {
            Sexp::Atom(a) if &**a == "i0" || &**a == "i1" => Ok(s.clone()),
            Sexp::Atom(a) => index(&names.dimensions, a)
                .map(dim)
                .ok_or_else(|| format!("unknown dimension {a}")),
            Sexp::List(xs) => match (xs.first().map(Sexp::atom).transpose()?, &xs[1..]) {
                (Some("neg"), [r]) => Ok(call("neg", [self.interval(r, names)?])),
                (Some(op @ ("meet" | "join")), [r, s]) => Ok(call(
                    op,
                    [self.interval(r, names)?, self.interval(s, names)?],
                )),
                _ => Err(format!("invalid interval {s}")),
            },
        }
    }

    fn term(&mut self, s: &Sexp, names: &Names) -> Result<Sexp> {
        let xs = match s {
            Sexp::Atom(a) => {
                return if ["bool", "btrue", "bfalse", "nat", "zero"].contains(&&**a) {
                    Ok(s.clone())
                } else if let Ok(n) = a.parse::<usize>()
                    && a.bytes().all(|c| c.is_ascii_digit())
                {
                    if n > 10_000 {
                        return Err(format!("numeral {n} is too large"));
                    }
                    Ok((0..n).fold(atom("zero"), |t, _| call("suc", [t])))
                } else if let Some(i) = index(&names.ordinary, &**a) {
                    Ok(v(i))
                } else if let Some(d) = data::by_name(a) {
                    if d.params == 0 {
                        Ok(atom(&d.ty))
                    } else {
                        Err(format!("{a} needs {} type parameters", d.params))
                    }
                } else if let Some((d, i)) = data::by_ctor_name(a) {
                    let c = &d.ctors[i];
                    if c.args.is_empty() {
                        Ok(atom(&c.symbol))
                    } else {
                        Err(format!("constructor {a} needs {} arguments", c.args.len()))
                    }
                } else if let Some(t) = self.defs.get(&**a) {
                    Ok(t.clone())
                } else if let Some(t) = self.prelude.get(&**a) {
                    Ok(t.clone())
                } else {
                    Err(format!("unknown name {a}"))
                };
            }
            Sexp::List(xs) => xs,
        };
        let head = xs.first().ok_or("empty term")?.atom()?;
        let args = &xs[1..];
        Ok(match (head, args) {
            ("u", [l]) => u(level(l)?),
            (former @ ("pi" | "sigma"), [x, a, b]) => {
                let a = self.term(a, names)?;
                let b = self.term(b, &names.with_ordinary(binder(x)?))?;
                call(former, [a, b])
            }
            ("lam", [x, _domain, body]) => {
                // The domain is checked where the lambda meets its expected
                // type; the core lambda carries no annotation.
                call("lam", [self.term(body, &names.with_ordinary(binder(x)?))?])
            }
            ("app", [f, rest @ ..]) if !rest.is_empty() => {
                let mut out = self.term(f, names)?;
                for a in rest {
                    out = call("app", [out, self.term(a, names)?]);
                }
                out
            }
            ("pair", [a, b]) => call("pair", [self.term(a, names)?, self.term(b, names)?]),
            (proj @ ("fst" | "snd"), [t]) => call(proj, [self.term(t, names)?]),
            ("plam", [i, body]) => {
                call("plam", [self.term(body, &names.with_dimension(binder(i)?))?])
            }
            ("path", [i, a, l, r]) => path(
                self.term(a, &names.with_dimension(binder(i)?))?,
                self.term(l, names)?,
                self.term(r, names)?,
            ),
            ("path", [a, l, r]) => path(
                self.term(a, &names.with_dimension("_"))?,
                self.term(l, names)?,
                self.term(r, names)?,
            ),
            ("papp", [p, r]) => papp(self.term(p, names)?, self.interval(r, names)?),
            ("suc", [n]) => call("suc", [self.term(n, names)?]),
            (head @ ("bif" | "natrec"), [c, motive, t, f, b]) => call(
                head,
                [
                    self.term(motive, &names.with_ordinary(binder(c)?))?,
                    self.term(t, names)?,
                    self.term(f, names)?,
                    self.term(b, names)?,
                ],
            ),
            ("ann", [t, a]) => call("ann", [self.term(t, names)?, self.term(a, names)?]),
            ("elim", [ty, rest @ ..]) => {
                let d = data::by_name(ty.atom()?).ok_or_else(|| format!("unknown data type {ty}"))?;
                // `(elim T k P (METHODS) x)`, or with parameters
                // `(elim T (PARAMS) k P (METHODS) x)`.
                let (params, k, motive, methods, x) = match rest {
                    [k, motive, methods, x] if d.params == 0 => (&[][..], k, motive, methods, x),
                    [params, k, motive, methods, x] => (params.list()?, k, motive, methods, x),
                    _ => return Err(format!("invalid elim {s}")),
                };
                if params.len() != d.params {
                    return Err(format!("elim {} needs {} parameters", d.name, d.params));
                }
                let methods = methods.list()?;
                if methods.len() != d.ctors.len() {
                    return Err(format!("elim {} needs {} methods", d.name, d.ctors.len()));
                }
                let mut items = Vec::new();
                for a in params {
                    items.push(self.term(a, names)?);
                }
                items.push(self.term(motive, &names.with_ordinary(binder(k)?))?);
                for m in methods {
                    items.push(self.term(m, names)?);
                }
                items.push(self.term(x, names)?);
                call(&d.elim, items)
            }
            (c, args) if data::by_ctor_name(c).is_some() => {
                // Parameters are not written: `(cons btrue nil)`. They come
                // from the fields or from the expected type.
                let (d, i) = data::by_ctor_name(c).unwrap();
                let ctor = &d.ctors[i];
                if args.len() != ctor.args.len() {
                    return Err(format!("constructor {c} needs {} arguments", ctor.args.len()));
                }
                let args = args.iter().map(|a| self.term(a, names)).collect::<Result<Vec<_>>>()?;
                data::apply(&ctor.symbol, args)
            }
            (n, args) if data::by_name(n).is_some() => {
                let d = data::by_name(n).unwrap();
                if args.len() != d.params {
                    return Err(format!("{n} needs {} type parameters", d.params));
                }
                let args = args.iter().map(|a| self.term(a, names)).collect::<Result<Vec<_>>>()?;
                data::apply(&d.ty, args)
            }
            ("equiv", [a, b]) => {
                let (a, b) = (self.term(a, names)?, self.term(b, names)?);
                self.p.equiv_type(&a, &b)?.0
            }
            ("transport", [i, a, x]) => call(
                "comp",
                [
                    self.term(a, &names.with_dimension(binder(i)?))?,
                    atom("ff"),
                    atom("zero"),
                    self.term(x, names)?,
                ],
            ),
            _ => return Err(format!("invalid term {s}")),
        })
    }

    /// Register a data declaration and return its generated theory text.
    fn declare(&mut self, head: &Sexp, ctors: &[Sexp]) -> Result<String> {
        // `NAME` or `(NAME PARAM...)`.
        let (name, params): (&str, Vec<&str>) = match head {
            Sexp::Atom(a) => (a, vec![]),
            Sexp::List(xs) if !xs.is_empty() => (
                xs[0].atom()?,
                xs[1..].iter().map(Sexp::atom).collect::<Result<_>>()?,
            ),
            _ => return Err(format!("invalid data head {head}")),
        };
        self.fresh(name)?;
        for (j, p) in params.iter().enumerate() {
            binder(&atom(p))?;
            if params[..j].contains(p) {
                return Err(format!("duplicate parameter {p}"));
            }
        }
        let ty = format!("ty/{name}");
        let mut out = Vec::new();
        for c in ctors {
            let xs = c.list()?;
            let cname = xs.first().ok_or("empty constructor")?.atom()?;
            self.fresh(cname)?;
            if out.iter().any(|o: &Ctor| o.name == cname) {
                return Err(format!("duplicate constructor {cname}"));
            }
            let mut args = Vec::new();
            for a in &xs[1..] {
                // Fields: discrete closed types, a parameter, or the type
                // itself at its own parameters (uniform recursion).
                let own = Sexp::List(
                    std::iter::once(atom(name))
                        .chain(params.iter().map(|p| atom(p)))
                        .collect(),
                );
                let arg = match a {
                    Sexp::Atom(n) if &**n == "bool" || &**n == "nat" => ArgTy::Closed(atom(n)),
                    Sexp::Atom(n) if &**n == name && params.is_empty() => ArgTy::Rec,
                    _ if params.is_empty() == false && *a == own => ArgTy::Rec,
                    Sexp::Atom(n) if params.contains(&&**n) => {
                        ArgTy::Param(params.iter().position(|p| *p == &**n).unwrap())
                    }
                    Sexp::Atom(n) => match data::by_name(n) {
                        Some(d) if d.params == 0 => ArgTy::Closed(atom(&d.ty)),
                        _ => {
                            return Err(format!(
                                "field {n} must be bool, nat, a parameter, the type itself or an earlier closed data type"
                            ));
                        }
                    },
                    _ => return Err(format!("invalid field type {a}")),
                };
                args.push(arg);
            }
            out.push(Ctor {
                name: cname.to_owned(),
                symbol: format!("ctor/{name}/{cname}"),
                args,
            });
        }
        if out.is_empty() {
            return Err(format!("data {name} needs a constructor"));
        }
        let d = data::register(Data {
            name: name.to_owned(),
            ty,
            elim: format!("elim/{name}"),
            params: params.len(),
            ctors: out,
        });
        Ok(d.theory())
    }

    fn fresh(&self, name: &str) -> Result<()> {
        if data::by_name(name).is_some() || data::by_ctor_name(name).is_some() {
            return Err(format!("{name} is already declared"));
        }
        if self.defs.contains_key(name) || self.prelude.contains_key(name) {
            return Err(format!("{name} is already defined"));
        }
        binder(&atom(name)).map(|_| ())
    }
}

/// Pretty-print a closed core value: unary levels become decimal.
fn show(s: &Sexp) -> String {
    fn unary(s: &Sexp) -> Option<usize> {
        match s {
            Sexp::Atom(a) if &**a == "z" => Some(0),
            Sexp::List(xs) if xs.len() == 2 && xs[0] == atom("s") => unary(&xs[1]).map(|n| n + 1),
            _ => None,
        }
    }
    fn numeral(s: &Sexp) -> Option<usize> {
        match s {
            Sexp::Atom(a) if &**a == "zero" => Some(0),
            Sexp::List(xs) if xs.len() == 2 && xs[0] == atom("suc") => numeral(&xs[1]).map(|n| n + 1),
            _ => None,
        }
    }
    if let Some(n) = numeral(s) {
        return n.to_string();
    }
    match s {
        // Generated symbols print as the names they were declared with.
        Sexp::Atom(a) if a.starts_with("ctor/") || a.starts_with("ty/") => {
            a.rsplit('/').next().unwrap_or(a).to_string()
        }
        Sexp::Atom(a) => a.to_string(),
        Sexp::List(xs) => {
            let parts: Vec<_> = xs
                .iter()
                .enumerate()
                .map(|(i, x)| match unary(x) {
                    Some(n) if i > 0 => n.to_string(),
                    _ => show(x),
                })
                .collect();
            format!("({})", parts.join(" "))
        }
    }
}

pub fn run(source: &str) -> Result<Script> {
    let source = source.to_owned();
    // Terms are interned per thread, so parsing happens on the worker.
    let (certified, evaluations) = certify(move || {
        let forms = parse(&source)?;
        data::clear();
        let mut appended = String::new();
        let mut e = Elaborator::new()?;
        let nil = atom("nil");
        let top = Face::True;
        let mut evaluations = Vec::new();
        let mut names_seen = std::collections::HashSet::new();
        for form in &forms {
            let xs = form.list()?;
            let head = xs.first().ok_or("empty form")?.atom()?;
            // A data head may be `(NAME PARAM...)`.
            let name = match xs.get(1).ok_or("form needs a name")? {
                Sexp::List(h) if head == "data" && !h.is_empty() => h[0].atom()?.to_owned(),
                other => other.atom()?.to_owned(),
            };
            if !names_seen.insert(name.clone()) {
                return Err(format!("duplicate name {name}"));
            }
            let empty = Names::default();
            match (head, &xs[2..]) {
                ("data", ctors) => appended.push_str(&e.declare(&xs[1], ctors)?),
                ("def", [ty, t]) => {
                    e.fresh(&name)?;
                    let ty = e.term(ty, &empty)?;
                    let t = e.term(t, &empty)?;
                    let id = e
                        .p
                        .check(0, &nil, &top, &t, &ty)
                        .map_err(|err| format!("def {name}: {err}"))?;
                    e.p.f.path.p.result(&name, id);
                    e.defs.insert(name, call("ann", [t, ty]));
                }
                ("check", [t, ty]) => {
                    let ty = e.term(ty, &empty)?;
                    let t = e.term(t, &empty)?;
                    let id = e
                        .p
                        .check(0, &nil, &top, &t, &ty)
                        .map_err(|err| format!("check {name}: {err}"))?;
                    e.p.f.path.p.result(&name, id);
                }
                ("eval", [t, rest @ ..]) if rest.len() <= 1 => {
                    let t = e.term(t, &empty)?;
                    let ty = match rest {
                        [ty] => e.term(ty, &empty)?,
                        _ => {
                            // Report the inferred type in weak-head normal form.
                            let fail = |err| format!("eval {name}: {err}");
                            let (ty, _) = e.p.infer(0, &nil, &top, &t).map_err(fail)?;
                            let (universe, _) = e.p.infer(0, &nil, &top, &ty).map_err(fail)?;
                            e.p.value(0, &nil, &top, &ty, &universe, FUEL).map_err(fail)?.0
                        }
                    };
                    let (value, id) = e
                        .p
                        .value(0, &nil, &top, &t, &ty, FUEL)
                        .map_err(|err| format!("eval {name}: {err}"))?;
                    e.p.f.path.p.result(&name, id);
                    evaluations.push(Evaluation {
                        name,
                        value: show(&value),
                        ty: show(&ty),
                    });
                }
                ("equal", [a, b, ty]) => {
                    let (a, b, ty) = (e.term(a, &empty)?, e.term(b, &empty)?, e.term(ty, &empty)?);
                    let id = e
                        .p
                        .equality(0, &nil, &top, &a, &b, &ty)
                        .map_err(|err| format!("equal {name}: {err}"))?;
                    e.p.f.path.p.result(&name, id);
                }
                _ => return Err(format!("invalid form {form}")),
            }
        }
        Ok((e.p, evaluations, appended))
    })?;
    Ok(Script {
        certified,
        evaluations,
    })
}
