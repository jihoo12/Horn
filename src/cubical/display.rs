//! Print core terms the way a script writes them: variables and dimensions
//! by name, numerals as numbers, declared data by their declared names,
//! and definitions by their names instead of their inlined bodies. For
//! showing goals; nothing here is trusted or parsed back.
use super::engine::face_frontend::Face;
use super::engine::term::Sexp;
use std::collections::HashMap;

pub struct Printer<'a> {
    /// Closed terms to print as a name: definitions and prelude terms.
    pub known: &'a HashMap<Sexp, String>,
    /// How each hole `(hole K)` was written: `?1`, `?step`, ...
    pub holes: &'a [String],
    /// A level variable checked as a marker level: universe levels from the
    /// marker up print as the variable (`(u L)`, `(u (s L))`).
    pub level: Option<(usize, &'a str)>,
}

/// Names of the ordinary variables and dimensions in scope, outermost first.
#[derive(Clone, Default)]
pub struct Scope {
    pub vars: Vec<String>,
    pub dims: Vec<String>,
}

impl Scope {
    fn fresh(taken: &[String], base: &[&str]) -> String {
        for round in 0.. {
            for b in base {
                let name = if round == 0 {
                    (*b).to_owned()
                } else {
                    format!("{b}{round}")
                };
                if !taken.contains(&name) {
                    return name;
                }
            }
        }
        unreachable!()
    }
    fn with_var(&self) -> (Self, String) {
        let name = Self::fresh(&self.vars, &["x", "y", "z", "w"]);
        let mut out = self.clone();
        out.vars.push(name.clone());
        (out, name)
    }
    fn with_dim(&self) -> (Self, String) {
        let name = Self::fresh(&self.dims, &["i", "j", "k", "l"]);
        let mut out = self.clone();
        out.dims.push(name.clone());
        (out, name)
    }
    fn var(&self, k: usize) -> String {
        match self.vars.len().checked_sub(k + 1) {
            Some(i) => self.vars[i].clone(),
            None => format!("#{k}"),
        }
    }
    fn dim(&self, k: usize) -> String {
        match self.dims.len().checked_sub(k + 1) {
            Some(i) => self.dims[i].clone(),
            None => format!("#i{k}"),
        }
    }
}

fn unary(t: &Sexp) -> Option<usize> {
    match t {
        Sexp::Atom(a) if &**a == "z" => Some(0),
        Sexp::List(xs) if xs.len() == 2 && xs[0].atom().ok() == Some("s") => {
            unary(&xs[1]).map(|n| n + 1)
        }
        _ => None,
    }
}

fn numeral(t: &Sexp) -> Option<usize> {
    match t {
        Sexp::Atom(a) if &**a == "zero" => Some(0),
        Sexp::List(xs) if xs.len() == 2 && xs[0].atom().ok() == Some("suc") => {
            numeral(&xs[1]).map(|n| n + 1)
        }
        _ => None,
    }
}

/// A generated symbol's declared name: `ty/int` is `int`.
fn declared(symbol: &str) -> &str {
    if symbol.starts_with("ctor/") || symbol.starts_with("ty/") || symbol.starts_with("elim/") {
        symbol.rsplit('/').next().unwrap_or(symbol)
    } else {
        symbol
    }
}

impl Printer<'_> {
    pub fn term(&self, t: &Sexp, scope: &Scope) -> String {
        if let Some(name) = self.known.get(t) {
            return name.clone();
        }
        if let Some(n) = numeral(t) {
            return n.to_string();
        }
        let xs = match t {
            Sexp::Atom(a) => return declared(a).to_owned(),
            Sexp::List(xs) => xs,
        };
        let Some(head) = xs.first().and_then(|h| h.atom().ok()) else {
            return t.to_string();
        };
        let args = &xs[1..];
        match (head, args) {
            ("v", [k]) => match unary(k) {
                Some(k) => scope.var(k),
                None => t.to_string(),
            },
            ("u", [l]) => match (unary(l), self.level) {
                (Some(n), Some((mark, var))) if n >= mark => format!(
                    "(u {}{var}{})",
                    "(s ".repeat(n - mark),
                    ")".repeat(n - mark)
                ),
                (Some(n), _) => format!("(u {n})"),
                (None, _) => format!("(u {l})"),
            },
            (former @ ("pi" | "sigma"), [a, b]) => {
                let (inner, x) = scope.with_var();
                format!(
                    "({former} {x} {} {})",
                    self.term(a, scope),
                    self.term(b, &inner)
                )
            }
            ("lam", [b]) => {
                let (inner, x) = scope.with_var();
                format!("(lam {x} {})", self.term(b, &inner))
            }
            ("app", [_, _]) => {
                // Flatten nested applications: (app f a b).
                let mut parts = Vec::new();
                let mut f = t;
                while let Sexp::List(ys) = f
                    && ys.len() == 3
                    && ys[0].atom().ok() == Some("app")
                    && !self.known.contains_key(f)
                {
                    parts.push(self.term(&ys[2], scope));
                    f = &ys[1];
                }
                parts.push(self.term(f, scope));
                parts.reverse();
                format!("(app {})", parts.join(" "))
            }
            ("plam", [b]) => {
                let (inner, i) = scope.with_dim();
                format!("(plam {i} {})", self.term(b, &inner))
            }
            ("papp", [p, r]) => {
                format!("(papp {} {})", self.term(p, scope), self.interval(r, scope))
            }
            ("path", [a, l, r]) => {
                let (inner, i) = scope.with_dim();
                let family = self.term(a, &inner);
                if mentions(&family, &i) {
                    format!(
                        "(path {i} {family} {} {})",
                        self.term(l, scope),
                        self.term(r, scope)
                    )
                } else {
                    format!(
                        "(path {family} {} {})",
                        self.term(l, scope),
                        self.term(r, scope)
                    )
                }
            }
            ("ann", [x, _]) => self.term(x, scope),
            ("comp", [a, phi, tube, base]) => {
                let (inner, j) = scope.with_dim();
                if phi.atom().ok() == Some("ff") {
                    format!(
                        "(transport {j} {} {})",
                        self.term(a, &inner),
                        self.term(base, scope)
                    )
                } else {
                    format!(
                        "(comp {j} {} {} {} {})",
                        self.term(a, &inner),
                        self.face_syntax(phi, scope),
                        self.term(tube, &inner),
                        self.term(base, scope)
                    )
                }
            }
            ("system", [s]) => {
                let mut sides = Vec::new();
                let mut rest = s;
                while let Sexp::List(ys) = rest
                    && ys.len() == 4
                    && ys[0].atom().ok() == Some("side")
                {
                    sides.push(format!(
                        "({} {})",
                        self.face_syntax(&ys[1], scope),
                        self.term(&ys[2], scope)
                    ));
                    rest = &ys[3];
                }
                format!("(system {})", sides.join(" "))
            }
            (head @ ("bif" | "natrec"), [p, a, b, x]) => {
                let (inner, k) = scope.with_var();
                format!(
                    "({head} {k} {} {} {} {})",
                    self.term(p, &inner),
                    self.term(a, scope),
                    self.term(b, scope),
                    self.term(x, scope)
                )
            }
            ("loop", [r]) => format!("(loop {})", self.interval(r, scope)),
            ("hole", [k]) => k
                .atom()
                .ok()
                .and_then(|k| k.parse::<usize>().ok())
                .and_then(|k| self.holes.get(k).cloned())
                .unwrap_or_else(|| format!("?{k}")),
            (h, xs) if super::engine::data::motive_index(h).is_some_and(|m| m < xs.len()) => {
                // (elim T (PARAMS) k MOTIVE (METHODS) x): the motive binds one
                // variable.
                let m = super::engine::data::motive_index(h).unwrap();
                let (inner, k) = scope.with_var();
                let params: Vec<String> = xs[..m].iter().map(|x| self.term(x, scope)).collect();
                let methods: Vec<String> = xs[m + 1..xs.len() - 1]
                    .iter()
                    .map(|x| self.term(x, scope))
                    .collect();
                let params = if params.is_empty() {
                    String::new()
                } else {
                    format!(" ({})", params.join(" "))
                };
                format!(
                    "(elim {}{params} {k} {} ({}) {})",
                    declared(h),
                    self.term(&xs[m], &inner),
                    methods.join(" "),
                    self.term(&xs[xs.len() - 1], scope)
                )
            }
            (h, xs) => {
                let mut out = format!("({}", declared(h));
                for x in xs {
                    out.push(' ');
                    out.push_str(&self.term(x, scope));
                }
                out.push(')');
                out
            }
        }
    }

    pub fn interval(&self, r: &Sexp, scope: &Scope) -> String {
        match r {
            Sexp::Atom(a) if &**a == "i0" => "0".into(),
            Sexp::Atom(a) if &**a == "i1" => "1".into(),
            Sexp::List(xs) => match (xs.first().and_then(|h| h.atom().ok()), &xs[1..]) {
                (Some("dim"), [k]) => unary(k).map_or(r.to_string(), |k| scope.dim(k)),
                (Some("neg"), [x]) => format!("(neg {})", self.interval(x, scope)),
                (Some(op @ ("meet" | "join")), [x, y]) => format!(
                    "({op} {} {})",
                    self.interval(x, scope),
                    self.interval(y, scope)
                ),
                _ => r.to_string(),
            },
            _ => r.to_string(),
        }
    }

    /// A face, simplified: as a disjunction of conjunctions of endpoint
    /// conditions, without contradictory or subsumed conjunctions.
    pub fn face(&self, f: &Face, scope: &Scope) -> String {
        let mut clauses = dnf(f);
        clauses.sort();
        clauses.dedup();
        let kept: Vec<&Vec<(usize, bool)>> = clauses
            .iter()
            .filter(|c| {
                !clauses
                    .iter()
                    .any(|o| o != *c && o.iter().all(|l| c.contains(l)))
            })
            .collect();
        let literal = |(k, b): &(usize, bool)| format!("(= {} {})", scope.dim(*k), u8::from(*b));
        let clause = |c: &Vec<(usize, bool)>| match c.as_slice() {
            [] => "true".to_owned(),
            [l] => literal(l),
            ls => format!(
                "(and {})",
                ls.iter().map(literal).collect::<Vec<_>>().join(" ")
            ),
        };
        match kept.as_slice() {
            [] => "false".into(),
            [c] => clause(c),
            cs => format!(
                "(or {})",
                cs.iter().map(|c| clause(c)).collect::<Vec<_>>().join(" ")
            ),
        }
    }

    fn face_syntax(&self, phi: &Sexp, scope: &Scope) -> String {
        match Face::parse(phi) {
            Ok(f) => self.face(&f, scope),
            Err(_) => phi.to_string(),
        }
    }
}

/// Whether a printed term mentions the name as a whole word.
fn mentions(text: &str, name: &str) -> bool {
    text.split([' ', '(', ')']).any(|w| w == name)
}

/// A face as a disjunction of satisfiable conjunctions of endpoint
/// conditions, each sorted and without repeats.
fn dnf(f: &Face) -> Vec<Vec<(usize, bool)>> {
    match f {
        Face::False => vec![],
        Face::True => vec![vec![]],
        Face::End(k, b) => vec![vec![(*k, *b)]],
        Face::Or(a, b) => {
            let mut out = dnf(a);
            out.extend(dnf(b));
            out
        }
        Face::And(a, b) => {
            let (left, right) = (dnf(a), dnf(b));
            let mut out = Vec::new();
            for l in &left {
                for r in &right {
                    let mut c = l.clone();
                    c.extend(r.iter().copied());
                    c.sort();
                    c.dedup();
                    // i = 0 and i = 1 together hold nowhere.
                    if c.windows(2).all(|w| w[0].0 != w[1].0) {
                        out.push(c);
                    }
                }
            }
            out
        }
    }
}
