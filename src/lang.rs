//! A small surface language over Horn theories, in the style of Lean:
//! declare sorts, constructors, predicates and rules; define functions by
//! pattern matching; evaluate; state and prove theorems.
//!
//! ```text
//! sort Nat
//! ctor zero : Nat
//! ctor succ : Nat → Nat
//!
//! def add : Nat → Nat → Nat
//! | zero,   n => n
//! | succ m, n => succ (add m n)
//!
//! #eval add 2 3
//! theorem add_zero (n : Nat) : add n zero = n := by induction n
//! ```
//!
//! Nothing here is trusted. A function becomes a predicate with one more
//! argument, its result, and one rule per clause. `#eval` and `theorem`
//! are answered by proof search, and every answer becomes part of one
//! schematic certificate for the elaborated theory, which
//! `horn::schematic` checks; the certificate can also be exported for the
//! Agda model. Earlier theorems are used as lemmas by later proofs.
use crate::schematic;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::rc::Rc;

pub type Result<T> = std::result::Result<T, String>;

// ---------------------------------------------------------------------
// Syntax

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Ident(String),
    Meta(String),
    Num(u64),
    Sym(&'static str),
}

const KEYWORDS: &[&str] = &[
    "sort",
    "ctor",
    "pred",
    "rule",
    "def",
    "theorem",
    "by",
    "auto",
    "induction",
    "#eval",
    "#check",
];

fn lex(src: &str) -> Result<Vec<(Tok, usize)>> {
    let mut out = Vec::new();
    for (ln, line) in src.lines().enumerate() {
        let line = match line.find("--") {
            Some(i) => &line[..i],
            None => line,
        };
        let cs: Vec<char> = line.chars().collect();
        let mut i = 0;
        while i < cs.len() {
            let c = cs[i];
            if c.is_whitespace() {
                i += 1;
                continue;
            }
            let two: String = cs[i..cs.len().min(i + 2)].iter().collect();
            let sym = match two.as_str() {
                "->" => Some(("→", 2)),
                "=>" => Some(("=>", 2)),
                ":=" => Some((":=", 2)),
                _ => match c {
                    '→' => Some(("→", 1)),
                    '(' => Some(("(", 1)),
                    ')' => Some((")", 1)),
                    ':' => Some((":", 1)),
                    ',' => Some((",", 1)),
                    '|' => Some(("|", 1)),
                    '=' => Some(("=", 1)),
                    _ => None,
                },
            };
            if let Some((s, n)) = sym {
                out.push((Tok::Sym(s), ln + 1));
                i += n;
                continue;
            }
            let start = i;
            let word = |i: &mut usize| {
                while *i < cs.len()
                    && (cs[*i].is_alphanumeric() || matches!(cs[*i], '_' | '.' | '\'' | '#' | '?'))
                {
                    *i += 1;
                }
            };
            word(&mut i);
            if i == start {
                return Err(format!("line {}: unexpected character {c:?}", ln + 1));
            }
            let w: String = cs[start..i].iter().collect();
            let tok = if let Some(m) = w.strip_prefix('?') {
                Tok::Meta(m.to_owned())
            } else if w.chars().all(|c| c.is_ascii_digit()) {
                Tok::Num(
                    w.parse()
                        .map_err(|_| format!("line {}: bad numeral", ln + 1))?,
                )
            } else {
                Tok::Ident(w)
            };
            out.push((tok, ln + 1));
        }
    }
    Ok(out)
}

#[derive(Clone, Debug)]
enum Term {
    Name(String),
    Meta(String),
    Num(u64),
    App(String, Vec<Term>),
}

#[derive(Debug)]
enum Tactic {
    Auto,
    Induction(String),
}

#[derive(Debug)]
enum Decl {
    Sort(String),
    Ctor(String, Vec<String>, String),
    Pred(String, Vec<String>),
    Rule(String, Vec<Term>, Term),
    Def(String, Vec<String>, String, Vec<(Vec<Term>, Term)>),
    /// Name, binders, hypotheses, conclusion, tactic.
    Theorem(String, Vec<(String, String)>, Vec<Term>, Term, Tactic),
    Eval(Term),
    Check(Term),
}

struct Parser {
    toks: Vec<(Tok, usize)>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|t| &t.0)
    }

    fn line(&self) -> usize {
        self.toks
            .get(self.pos.min(self.toks.len().saturating_sub(1)))
            .map_or(0, |t| t.1)
    }

    fn err<T>(&self, msg: &str) -> Result<T> {
        Err(format!("line {}: {msg}", self.line()))
    }

    fn next(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).map(|t| t.0.clone());
        self.pos += 1;
        t
    }

    fn sym(&mut self, s: &str) -> Result<()> {
        match self.next() {
            Some(Tok::Sym(t)) if t == s => Ok(()),
            _ => {
                self.pos -= 1;
                self.err(&format!("expected `{s}`"))
            }
        }
    }

    fn is_sym(&self, s: &str) -> bool {
        matches!(self.peek(), Some(Tok::Sym(t)) if *t == s)
    }

    fn ident(&mut self) -> Result<String> {
        match self.next() {
            Some(Tok::Ident(w)) if !KEYWORDS.contains(&w.as_str()) => Ok(w),
            _ => {
                self.pos -= 1;
                self.err("expected a name")
            }
        }
    }

    fn keyword(&self) -> Option<&str> {
        match self.peek() {
            Some(Tok::Ident(w)) if KEYWORDS.contains(&w.as_str()) => Some(w),
            _ => None,
        }
    }

    /// `A → B → C`
    fn arrows(&mut self) -> Result<Vec<String>> {
        let mut xs = vec![self.ident()?];
        while self.is_sym("→") {
            self.pos += 1;
            xs.push(self.ident()?);
        }
        Ok(xs)
    }

    fn atom(&mut self) -> Result<Option<Term>> {
        if self.keyword().is_some() {
            return Ok(None);
        }
        Ok(match self.peek() {
            Some(Tok::Ident(_)) => Some(Term::Name(self.ident()?)),
            Some(Tok::Meta(m)) => {
                let m = m.clone();
                self.pos += 1;
                Some(Term::Meta(m))
            }
            Some(Tok::Num(n)) => {
                let n = *n;
                self.pos += 1;
                Some(Term::Num(n))
            }
            Some(Tok::Sym("(")) => {
                self.pos += 1;
                let t = self.term()?;
                self.sym(")")?;
                Some(t)
            }
            _ => None,
        })
    }

    /// Application by juxtaposition.
    fn app(&mut self) -> Result<Term> {
        let head = match self.atom()? {
            Some(t) => t,
            None => return self.err("expected a term"),
        };
        let mut args = Vec::new();
        while let Some(a) = self.atom()? {
            args.push(a);
        }
        Ok(match (head, args.is_empty()) {
            (t, true) => t,
            (Term::Name(f), false) => Term::App(f, args),
            _ => return self.err("only a name can be applied"),
        })
    }

    /// A judgment, possibly `f args = result`.
    fn term(&mut self) -> Result<Term> {
        let t = self.app()?;
        if self.is_sym("=") {
            self.pos += 1;
            let rhs = self.app()?;
            return Ok(match t {
                Term::App(f, mut args) => {
                    args.push(rhs);
                    Term::App(f, args)
                }
                Term::Name(f) => Term::App(f, vec![rhs]),
                _ => return self.err("the left of `=` must be a function call"),
            });
        }
        Ok(t)
    }

    fn decl(&mut self) -> Result<Decl> {
        let kw = match self.next() {
            Some(Tok::Ident(w)) if KEYWORDS.contains(&w.as_str()) => w,
            _ => {
                self.pos -= 1;
                return self.err("expected a declaration");
            }
        };
        Ok(match kw.as_str() {
            "sort" => Decl::Sort(self.ident()?),
            "ctor" => {
                let name = self.ident()?;
                self.sym(":")?;
                let mut sorts = self.arrows()?;
                let result = sorts.pop().expect("nonempty");
                Decl::Ctor(name, sorts, result)
            }
            "pred" => {
                let name = self.ident()?;
                self.sym(":")?;
                let mut sorts = self.arrows()?;
                if sorts.last().map(String::as_str) != Some("Prop") {
                    return self.err("a predicate's type ends in `Prop`");
                }
                sorts.pop();
                Decl::Pred(name, sorts)
            }
            "rule" => {
                let name = self.ident()?;
                self.sym(":")?;
                let mut js = vec![self.term()?];
                while self.is_sym("→") {
                    self.pos += 1;
                    js.push(self.term()?);
                }
                let concl = js.pop().expect("nonempty");
                Decl::Rule(name, js, concl)
            }
            "def" => {
                let name = self.ident()?;
                self.sym(":")?;
                let mut sorts = self.arrows()?;
                let result = sorts.pop().expect("nonempty");
                let mut clauses = Vec::new();
                while self.is_sym("|") {
                    self.pos += 1;
                    let mut pats = vec![self.app()?];
                    while self.is_sym(",") {
                        self.pos += 1;
                        pats.push(self.app()?);
                    }
                    self.sym("=>")?;
                    clauses.push((pats, self.app()?));
                }
                Decl::Def(name, sorts, result, clauses)
            }
            "theorem" => {
                let name = self.ident()?;
                let mut binders = Vec::new();
                while self.is_sym("(") {
                    self.pos += 1;
                    let mut names = vec![self.ident()?];
                    while !self.is_sym(":") {
                        names.push(self.ident()?);
                    }
                    self.sym(":")?;
                    let sort = self.ident()?;
                    self.sym(")")?;
                    binders.extend(names.into_iter().map(|n| (n, sort.clone())));
                }
                self.sym(":")?;
                let mut js = vec![self.term()?];
                while self.is_sym("→") {
                    self.pos += 1;
                    js.push(self.term()?);
                }
                let concl = js.pop().expect("nonempty");
                let tactic = if self.is_sym(":=") {
                    self.pos += 1;
                    match (self.next(), self.next()) {
                        (Some(Tok::Ident(b)), Some(Tok::Ident(t))) if b == "by" && t == "auto" => {
                            Tactic::Auto
                        }
                        (Some(Tok::Ident(b)), Some(Tok::Ident(t)))
                            if b == "by" && t == "induction" =>
                        {
                            Tactic::Induction(self.ident()?)
                        }
                        _ => {
                            self.pos -= 2;
                            return self.err("expected `by auto` or `by induction x`");
                        }
                    }
                } else {
                    Tactic::Auto
                };
                Decl::Theorem(name, binders, js, concl, tactic)
            }
            "#eval" => Decl::Eval(self.term()?),
            "#check" => Decl::Check(self.term()?),
            _ => return self.err(&format!("unexpected `{kw}`")),
        })
    }
}

fn parse(src: &str) -> Result<Vec<(Decl, usize)>> {
    let mut p = Parser {
        toks: lex(src)?,
        pos: 0,
    };
    let mut decls = Vec::new();
    while p.peek().is_some() {
        let line = p.line();
        decls.push((p.decl()?, line));
    }
    Ok(decls)
}

// ---------------------------------------------------------------------
// Search terms

/// A term during search: a logic variable, a rigid name (an eigenvariable
/// or case variable), or a symbol applied to terms.
#[derive(Clone, Debug)]
enum T {
    V(usize),
    E(u32),
    A(u32, Rc<[T]>),
}

#[derive(Clone)]
struct Rule {
    name: String,
    /// Variables are indices into `sorts`.
    sorts: Vec<u32>,
    premises: Vec<Pat>,
    conclusion: Pat,
}

#[derive(Clone, Debug)]
enum Pat {
    Var(usize),
    A(u32, Vec<Pat>),
    /// A rigid name; only in lemma statements.
    E(u32),
}

/// How a goal was proved.
#[derive(Clone)]
enum Just {
    Rule(usize),
    /// An earlier fact: a step of the certificate, with the instantiation
    /// of its statement's names.
    Fact(usize, Vec<(u32, T)>),
    /// A rule hypothesis or an earlier implication applied as a rule: its
    /// step, the instantiation of its names, and the proofs of its premises.
    Apply(usize, Vec<(u32, T)>),
}

#[derive(Clone)]
struct Proof {
    just: Just,
    goal: T,
    children: Vec<Proof>,
}

/// A usable fact: its statement and hypotheses, the names it generalizes
/// over (instances may replace them), and its step.
#[derive(Clone)]
struct Fact {
    stmt: Pat,
    premises: Vec<Pat>,
    names: Vec<u32>,
    step: usize,
}

/// A hypothesis in scope: plain (no premises, nothing generalized), or a
/// rule whose generalized names an application may instantiate.
#[derive(Clone)]
struct Hyp {
    premises: Vec<T>,
    concl: T,
    general: Vec<u32>,
    step: usize,
}

enum Work {
    Goal(T, u32),
    Build(Just, T, usize),
}

struct WNode {
    item: Work,
    next: WList,
}

type WList = Option<Rc<WNode>>;

struct PNode {
    proof: Proof,
    next: PList,
}

type PList = Option<Rc<PNode>>;

// ---------------------------------------------------------------------
// Elaboration

#[derive(Clone)]
struct Sig {
    sorts: Vec<String>,
    sort_ix: HashMap<String, u32>,
    /// Constructors and predicates share one numbering.
    names: Vec<String>,
    sym_ix: HashMap<String, u32>,
    inputs: Vec<Vec<u32>>,
    /// `None` for predicates.
    output: Vec<Option<u32>>,
    /// Functions: their predicate.
    defs: HashSet<String>,
    rules: Vec<Rule>,
    /// Names of eigenvariables and case variables, with sorts.
    rigid: Vec<(String, u32)>,
}

impl Sig {
    fn sort(&self, s: &str) -> Result<u32> {
        self.sort_ix
            .get(s)
            .copied()
            .ok_or_else(|| format!("unknown sort {s}"))
    }

    fn fresh_name(&self, base: &str) -> Result<()> {
        if self.sym_ix.contains_key(base) || self.sort_ix.contains_key(base) {
            return Err(format!("{base} is already declared"));
        }
        Ok(())
    }

    fn add_sym(&mut self, name: &str, inputs: Vec<u32>, output: Option<u32>) -> Result<()> {
        self.fresh_name(name)?;
        self.sym_ix.insert(name.to_owned(), self.names.len() as u32);
        self.names.push(name.to_owned());
        self.inputs.push(inputs);
        self.output.push(output);
        Ok(())
    }

    fn is_ctor(&self, name: &str) -> bool {
        self.sym_ix
            .get(name)
            .is_some_and(|&i| self.output[i as usize].is_some())
    }

    /// Numerals stand for `succ (… zero)` when those constructors exist.
    fn numeral(&self, n: u64) -> Result<Term> {
        if !(self.is_ctor("zero") && self.is_ctor("succ")) {
            return Err("numerals need constructors `zero` and `succ`".into());
        }
        let mut t = Term::Name("zero".into());
        for _ in 0..n {
            t = Term::App("succ".into(), vec![t]);
        }
        Ok(t)
    }
}

/// Collects rule variables and their sorts while compiling patterns.
struct Vars {
    names: Vec<String>,
    sorts: Vec<Option<u32>>,
}

impl Vars {
    fn get(&mut self, name: &str, sort: Option<u32>) -> Result<usize> {
        let i = match self.names.iter().position(|n| n == name) {
            Some(i) => i,
            None => {
                self.names.push(name.to_owned());
                self.sorts.push(None);
                self.names.len() - 1
            }
        };
        match (self.sorts[i], sort) {
            (Some(a), Some(b)) if a != b => Err(format!("variable {name} is used at two sorts")),
            (None, s) => {
                self.sorts[i] = s;
                Ok(i)
            }
            _ => Ok(i),
        }
    }
}

impl Sig {
    /// A pattern of the given sort (`None` for a judgment). Names that are
    /// not symbols are variables; `rigid` maps theorem binders.
    fn pattern(
        &self,
        t: &Term,
        sort: Option<u32>,
        vars: &mut Vars,
        rigid: &HashMap<String, u32>,
        judgment: bool,
    ) -> Result<Pat> {
        let (head, args): (&str, &[Term]) = match t {
            Term::Num(n) => return self.pattern(&self.numeral(*n)?, sort, vars, rigid, false),
            Term::Meta(m) => return Ok(Pat::Var(vars.get(&format!("?{m}"), sort)?)),
            Term::Name(n) if !self.sym_ix.contains_key(n.as_str()) => {
                if judgment {
                    return Err(format!("unknown predicate {n}"));
                }
                if let Some(&e) = rigid.get(n) {
                    if sort.is_some_and(|s| s != self.rigid[e as usize].1) {
                        return Err(format!("{n} has the wrong sort"));
                    }
                    return Ok(Pat::E(e));
                }
                return Ok(Pat::Var(vars.get(n, sort)?));
            }
            Term::Name(n) => (n.as_str(), &[]),
            Term::App(f, args) => (f.as_str(), args.as_slice()),
        };
        let i = *self
            .sym_ix
            .get(head)
            .ok_or_else(|| format!("unknown symbol {head}"))?;
        let inputs = &self.inputs[i as usize];
        if self.defs.contains(head) && !judgment {
            return Err(format!(
                "function {head} is called inside a term; statements may only have the form `{head} args = result` with no calls in args or result"
            ));
        }
        if self.output[i as usize] != sort && !(judgment && self.output[i as usize].is_none()) {
            return Err(format!("{head} cannot stand here"));
        }
        if inputs.len() != args.len() {
            return Err(format!("{head} takes {} arguments", inputs.len()));
        }
        let args = args
            .iter()
            .zip(inputs.clone())
            .map(|(a, s)| self.pattern(a, Some(s), vars, rigid, false))
            .collect::<Result<_>>()?;
        Ok(Pat::A(i, args))
    }

    fn rule(&mut self, name: String, premises: &[Term], concl: &Term) -> Result<()> {
        let mut vars = Vars {
            names: Vec::new(),
            sorts: Vec::new(),
        };
        let none = HashMap::new();
        let premises = premises
            .iter()
            .map(|p| self.pattern(p, None, &mut vars, &none, true))
            .collect::<Result<Vec<_>>>()?;
        let conclusion = self.pattern(concl, None, &mut vars, &none, true)?;
        let sorts = vars
            .sorts
            .iter()
            .zip(&vars.names)
            .map(|(s, n)| s.ok_or_else(|| format!("cannot tell the sort of {n} in rule {name}")))
            .collect::<Result<_>>()?;
        self.rules.push(Rule {
            name,
            sorts,
            premises,
            conclusion,
        });
        Ok(())
    }

    /// `f p₁ … pₙ = rhs` becomes a rule: calls inside rhs become premises
    /// with fresh result variables.
    fn clause(&mut self, f: &str, n: usize, pats: &[Term], rhs: &Term) -> Result<()> {
        let mut premises = Vec::new();
        let mut fresh = 0;
        let rhs = self.flatten(rhs, &mut premises, &mut fresh)?;
        let mut args = pats.to_vec();
        args.push(rhs);
        self.rule(
            format!("{f}.{n}"),
            &premises,
            &Term::App(f.to_owned(), args),
        )
    }

    fn flatten(&self, t: &Term, premises: &mut Vec<Term>, fresh: &mut usize) -> Result<Term> {
        match t {
            Term::App(g, args) => {
                let args = args
                    .iter()
                    .map(|a| self.flatten(a, premises, fresh))
                    .collect::<Result<Vec<_>>>()?;
                if self.defs.contains(g) {
                    *fresh += 1;
                    let v = Term::Name(format!("result.{fresh}"));
                    let mut call = args;
                    call.push(v.clone());
                    premises.push(Term::App(g.clone(), call));
                    Ok(v)
                } else {
                    Ok(Term::App(g.clone(), args))
                }
            }
            Term::Name(g) if self.defs.contains(g) => {
                *fresh += 1;
                let v = Term::Name(format!("result.{fresh}"));
                premises.push(Term::App(g.clone(), vec![v.clone()]));
                Ok(v)
            }
            t => Ok(t.clone()),
        }
    }

    /// A judgment with the calls in its arguments flattened into premises.
    fn flatten_judgment(
        &self,
        t: &Term,
        premises: &mut Vec<Term>,
        fresh: &mut usize,
    ) -> Result<Term> {
        match t {
            Term::App(p, args) => {
                let args = args
                    .iter()
                    .map(|a| self.flatten(a, premises, fresh))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Term::App(p.clone(), args))
            }
            t => Ok(t.clone()),
        }
    }

    fn theory_text(&self) -> String {
        let mut s = String::new();
        for name in &self.sorts {
            let _ = writeln!(s, "(sort {name})");
        }
        for (i, name) in self.names.iter().enumerate() {
            let ins: Vec<&str> = self.inputs[i]
                .iter()
                .map(|&x| self.sorts[x as usize].as_str())
                .collect();
            match self.output[i] {
                Some(o) => {
                    let _ = writeln!(
                        s,
                        "(ctor {name} ({}) {})",
                        ins.join(" "),
                        self.sorts[o as usize]
                    );
                }
                None => {
                    let _ = writeln!(s, "(pred {name} ({}))", ins.join(" "));
                }
            }
        }
        for r in &self.rules {
            let ps: Vec<String> = r.premises.iter().map(|p| self.pat_text(p)).collect();
            let _ = writeln!(
                s,
                "(rule {} ({}) {})",
                r.name,
                ps.join(" "),
                self.pat_text(&r.conclusion)
            );
        }
        s
    }

    fn pat_text(&self, p: &Pat) -> String {
        match p {
            Pat::Var(v) => format!("?v{v}"),
            Pat::E(e) => self.rigid[*e as usize].0.clone(),
            Pat::A(f, args) if args.is_empty() && self.output[*f as usize].is_some() => {
                self.names[*f as usize].clone()
            }
            Pat::A(f, args) => {
                let args: Vec<String> = args.iter().map(|a| self.pat_text(a)).collect();
                let sep = if args.is_empty() { "" } else { " " };
                format!("({}{sep}{})", self.names[*f as usize], args.join(" "))
            }
        }
    }
}

// ---------------------------------------------------------------------
// Proof search

struct Prover {
    sig: Rc<Sig>,
    binding: Vec<Option<T>>,
    var_sort: Vec<u32>,
    trail: Vec<usize>,
    facts: Vec<Fact>,
    /// Hypotheses in scope.
    hyps: Vec<Hyp>,
    budget: u64,
    /// Steps per depth bound, and the largest bound.
    round: u64,
    max_depth: u32,
    /// Whether the depth bound cut off some branch.
    cut: bool,
}

impl Prover {
    fn fresh(&mut self, sort: u32) -> T {
        self.binding.push(None);
        self.var_sort.push(sort);
        T::V(self.binding.len() - 1)
    }

    fn walk(&self, t: &T) -> T {
        let mut t = t.clone();
        while let T::V(v) = t {
            match &self.binding[v] {
                Some(u) => t = u.clone(),
                None => break,
            }
        }
        t
    }

    fn occurs(&self, v: usize, t: &T) -> bool {
        match self.walk(t) {
            T::V(w) => v == w,
            T::E(_) => false,
            T::A(_, args) => args.iter().any(|a| self.occurs(v, a)),
        }
    }

    fn unify(&mut self, a: &T, b: &T) -> bool {
        match (self.walk(a), self.walk(b)) {
            (T::V(x), T::V(y)) if x == y => true,
            (T::V(x), t) | (t, T::V(x)) => {
                if self.occurs(x, &t) {
                    return false;
                }
                self.binding[x] = Some(t);
                self.trail.push(x);
                true
            }
            (T::E(x), T::E(y)) => x == y,
            (T::A(f, xs), T::A(g, ys)) => {
                f == g
                    && xs.len() == ys.len()
                    && xs.iter().zip(ys.iter()).all(|(x, y)| self.unify(x, y))
            }
            _ => false,
        }
    }

    fn undo(&mut self, mark: usize) {
        while self.trail.len() > mark {
            let v = self.trail.pop().expect("nonempty");
            self.binding[v] = None;
        }
    }

    /// Instantiate a pattern; `env` holds the variables made so far and
    /// `names` the rigid names to replace.
    fn inst(&mut self, p: &Pat, env: &mut Vec<Option<T>>, sorts: &[u32], names: &[(u32, T)]) -> T {
        match p {
            Pat::Var(v) => {
                if env[*v].is_none() {
                    env[*v] = Some(self.fresh(sorts[*v]));
                }
                env[*v].clone().expect("set")
            }
            Pat::E(e) => names
                .iter()
                .find(|(n, _)| n == e)
                .map_or(T::E(*e), |(_, t)| t.clone()),
            Pat::A(f, args) => {
                let args: Vec<T> = args
                    .iter()
                    .map(|a| self.inst(a, env, sorts, names))
                    .collect();
                T::A(*f, args.into())
            }
        }
    }

    fn solve(&mut self, work: WList, proofs: PList) -> Option<PList> {
        if self.budget == 0 {
            return None;
        }
        self.budget -= 1;
        let Some(node) = work else {
            return Some(proofs);
        };
        match &node.item {
            Work::Build(just, goal, n) => {
                let mut children = Vec::new();
                let mut ps = proofs;
                for _ in 0..*n {
                    let p = ps.expect("enough proofs");
                    children.push(p.proof.clone());
                    ps = p.next.clone();
                }
                children.reverse();
                let proof = Proof {
                    just: just.clone(),
                    goal: goal.clone(),
                    children,
                };
                self.solve(node.next.clone(), Some(Rc::new(PNode { proof, next: ps })))
            }
            Work::Goal(goal, depth) => {
                if *depth == 0 {
                    self.cut = true;
                    return None;
                }
                // Hypotheses first, then earlier theorems, then rules. A
                // rule hypothesis or an implication becomes subgoals.
                for i in 0..self.hyps.len() {
                    let mark = self.trail.len();
                    let h = self.hyps[i].clone();
                    let names: Vec<(u32, T)> = h
                        .general
                        .iter()
                        .map(|&e| (e, self.fresh(self.sig.rigid[e as usize].1)))
                        .collect();
                    let concl = subst_names(&h.concl, &names);
                    if self.unify(goal, &concl) {
                        let r = if h.premises.is_empty() && h.general.is_empty() {
                            let next = cons(
                                Work::Build(Just::Fact(h.step, Vec::new()), goal.clone(), 0),
                                &node.next,
                            );
                            self.solve(next, proofs.clone())
                        } else {
                            let mut next = cons(
                                Work::Build(
                                    Just::Apply(h.step, names.clone()),
                                    goal.clone(),
                                    h.premises.len(),
                                ),
                                &node.next,
                            );
                            for p in h.premises.iter().rev() {
                                next = cons(Work::Goal(subst_names(p, &names), depth - 1), &next);
                            }
                            self.solve(next, proofs.clone())
                        };
                        if let Some(r) = r {
                            return Some(r);
                        }
                    }
                    self.undo(mark);
                }
                // Earlier theorems without premises, then the rules, then
                // theorems with premises, which make deeper subgoals.
                for i in 0..self.facts.len() {
                    if self.facts[i].premises.is_empty()
                        && let Some(r) = self.try_fact(i, goal, *depth, &node.next, &proofs)
                    {
                        return Some(r);
                    }
                }
                for r in 0..self.sig.rules.len() {
                    let mark = self.trail.len();
                    let rule = &self.sig.rules[r];
                    let mut env = vec![None; rule.sorts.len()];
                    let concl =
                        self.inst(&rule.conclusion.clone(), &mut env, &rule.sorts.clone(), &[]);
                    if self.unify(goal, &concl) {
                        let rule = &self.sig.rules[r];
                        let premises = rule.premises.clone();
                        let sorts = rule.sorts.clone();
                        let mut next = cons(
                            Work::Build(Just::Rule(r), goal.clone(), premises.len()),
                            &node.next,
                        );
                        for p in premises.iter().rev() {
                            let t = self.inst(p, &mut env, &sorts, &[]);
                            next = cons(Work::Goal(t, depth - 1), &next);
                        }
                        if let Some(r) = self.solve(next, proofs.clone()) {
                            return Some(r);
                        }
                    }
                    self.undo(mark);
                }
                for i in 0..self.facts.len() {
                    if !self.facts[i].premises.is_empty()
                        && let Some(r) = self.try_fact(i, goal, *depth, &node.next, &proofs)
                    {
                        return Some(r);
                    }
                }
                None
            }
        }
    }

    fn try_fact(
        &mut self,
        i: usize,
        goal: &T,
        depth: u32,
        next: &WList,
        proofs: &PList,
    ) -> Option<PList> {
        let mark = self.trail.len();
        let fact = self.facts[i].clone();
        let names: Vec<(u32, T)> = fact
            .names
            .iter()
            .map(|&e| (e, self.fresh(self.sig.rigid[e as usize].1)))
            .collect();
        let stmt = self.inst(&fact.stmt, &mut Vec::new(), &[], &names);
        if self.unify(goal, &stmt) {
            let just = if fact.premises.is_empty() {
                Just::Fact(fact.step, names.clone())
            } else {
                Just::Apply(fact.step, names.clone())
            };
            let mut next = cons(Work::Build(just, goal.clone(), fact.premises.len()), next);
            for p in fact.premises.iter().rev() {
                let t = self.inst(p, &mut Vec::new(), &[], &names);
                next = cons(Work::Goal(t, depth - 1), &next);
            }
            if let Some(r) = self.solve(next, proofs.clone()) {
                return Some(r);
            }
        }
        self.undo(mark);
        None
    }

    /// Search with increasing depth.
    fn prove(&mut self, goal: &T) -> Option<Proof> {
        let mut depth = 4;
        while depth <= self.max_depth {
            self.budget = self.round;
            self.cut = false;
            let mark = self.trail.len();
            let work = cons(Work::Goal(goal.clone(), depth), &None);
            if let Some(Some(p)) = self.solve(work, None) {
                return Some(p.proof.clone());
            }
            self.undo(mark);
            // The whole tree was explored: a deeper bound cannot help.
            if self.budget > 0 && !self.cut {
                break;
            }
            depth *= 2;
        }
        None
    }
}

fn cons(item: Work, next: &WList) -> WList {
    Some(Rc::new(WNode {
        item,
        next: next.clone(),
    }))
}

// ---------------------------------------------------------------------
// Certificates

struct Cert {
    goals: String,
    proof: String,
    steps: usize,
    /// Hypothesis-free judgments already derived, by text.
    derived: HashMap<String, usize>,
    /// For each step, the hypothesis steps it depends on.
    deps: Vec<Vec<usize>>,
    /// Hypothesis steps.
    hyps: HashSet<usize>,
}

impl Cert {
    fn line(&mut self, s: String, mut deps: Vec<usize>) -> usize {
        let n = self.steps;
        let _ = writeln!(self.proof, "{s}");
        self.steps += 1;
        deps.sort_unstable();
        deps.dedup();
        self.deps.push(deps);
        n
    }
}

struct Session {
    sig: Sig,
    cert: Cert,
    facts: Vec<Fact>,
    report: Vec<String>,
    goal_count: usize,
}

impl Session {
    fn text(&self, t: &T) -> String {
        match t {
            T::V(_) => unreachable!("resolved"),
            T::E(e) => self.sig.rigid[*e as usize].0.clone(),
            T::A(f, args) if args.is_empty() && self.sig.output[*f as usize].is_some() => {
                self.sig.names[*f as usize].clone()
            }
            T::A(f, args) => {
                let args: Vec<String> = args.iter().map(|a| self.text(a)).collect();
                let sep = if args.is_empty() { "" } else { " " };
                format!("({}{sep}{})", self.sig.names[*f as usize], args.join(" "))
            }
        }
    }

    /// Surface syntax, with numerals.
    fn show(&self, t: &T) -> String {
        let mut n = 0;
        let mut u = t;
        loop {
            match u {
                T::A(f, args) if self.sig.names[*f as usize] == "succ" && args.len() == 1 => {
                    n += 1;
                    u = &args[0];
                }
                T::A(f, args) if self.sig.names[*f as usize] == "zero" && args.is_empty() => {
                    return n.to_string();
                }
                _ => break,
            }
        }
        let arg = |a: &T| {
            let s = self.show(a);
            if matches!(a, T::A(_, xs) if !xs.is_empty()) && s.contains(' ') {
                format!("({s})")
            } else {
                s
            }
        };
        match t {
            T::V(_) => "_".into(),
            // A theorem's variable is shown by its binder name.
            T::E(e) => {
                let name = &self.sig.rigid[*e as usize].0;
                name.rsplit('.').next().unwrap_or(name).to_owned()
            }
            T::A(f, args) if args.is_empty() => self.sig.names[*f as usize].clone(),
            // A function judgment is shown as an equation.
            T::A(f, args) if self.sig.defs.contains(&self.sig.names[*f as usize]) => {
                let (last, init) = args.split_last().expect("nonempty");
                let init: Vec<String> = init.iter().map(arg).collect();
                let sep = if init.is_empty() { "" } else { " " };
                format!(
                    "{}{sep}{} = {}",
                    self.sig.names[*f as usize],
                    init.join(" "),
                    self.show(last)
                )
            }
            T::A(f, args) => {
                let args: Vec<String> = args.iter().map(arg).collect();
                format!("{} {}", self.sig.names[*f as usize], args.join(" "))
            }
        }
    }

    /// The smallest closed term of a sort, for variables a proof leaves open.
    fn inhabitant(&self, sort: u32) -> Result<T> {
        let mut known: HashMap<u32, T> = HashMap::new();
        loop {
            let before = known.len();
            for (i, out) in self.sig.output.iter().enumerate() {
                let Some(o) = out else { continue };
                if known.contains_key(o) {
                    continue;
                }
                let args: Option<Vec<T>> = self.sig.inputs[i]
                    .iter()
                    .map(|s| known.get(s).cloned())
                    .collect();
                if let Some(args) = args {
                    known.insert(*o, T::A(i as u32, args.into()));
                }
            }
            if known.len() == before {
                break;
            }
        }
        known
            .get(&sort)
            .cloned()
            .ok_or_else(|| format!("sort {} has no closed terms", self.sig.sorts[sort as usize]))
    }

    fn close(&self, pr: &Prover, t: &T) -> Result<T> {
        Ok(match pr.walk(t) {
            T::V(v) => self.inhabitant(pr.var_sort[v])?,
            T::E(e) => T::E(e),
            T::A(f, args) => T::A(
                f,
                args.iter()
                    .map(|a| self.close(pr, a))
                    .collect::<Result<Vec<_>>>()?
                    .into(),
            ),
        })
    }

    /// The hypotheses a reference depends on, as the checker computes them.
    fn deps_of(&self, r: &str) -> Vec<usize> {
        r.parse::<usize>()
            .map_or_else(|_| Vec::new(), |n| self.cert.deps[n].clone())
    }

    /// `(X t)…` for an instantiation.
    fn bindings(&self, pr: &Prover, names: &[(u32, T)]) -> Result<Vec<String>> {
        names
            .iter()
            .map(|(e, t)| {
                let t = self.close(pr, t)?;
                Ok(format!(
                    "({} {})",
                    self.sig.rigid[*e as usize].0,
                    self.text(&t)
                ))
            })
            .collect()
    }

    /// Write a proof; returns how to refer to its conclusion.
    fn emit(&mut self, pr: &Prover, p: &Proof) -> Result<String> {
        let goal = self.close(pr, &p.goal)?;
        let text = self.text(&goal);
        match &p.just {
            Just::Fact(step, names) if names.is_empty() => Ok(step.to_string()),
            Just::Fact(step, names) => {
                Ok(format!("({step} {})", self.bindings(pr, names)?.join(" ")))
            }
            Just::Apply(step, names) => {
                let binds = self.bindings(pr, names)?;
                let mut refs = Vec::new();
                let mut deps = Vec::new();
                for c in &p.children {
                    let r = self.emit(pr, c)?;
                    deps.extend(self.deps_of(&r));
                    refs.push(r);
                }
                // A rule hypothesis stays a hypothesis of the result; an
                // earlier theorem's hypotheses are discharged by the refs.
                if self.cert.hyps.contains(step) {
                    deps.push(*step);
                }
                let n = self.cert.line(
                    format!(
                        "(apply {} {step} ({}) ({}))",
                        self.cert.steps,
                        binds.join(" "),
                        refs.join(" ")
                    ),
                    deps,
                );
                Ok(n.to_string())
            }
            Just::Rule(r) => {
                if let Some(&n) = self.cert.derived.get(&text) {
                    return Ok(n.to_string());
                }
                let mut refs = Vec::new();
                let mut deps = Vec::new();
                for c in &p.children {
                    let r = self.emit(pr, c)?;
                    deps.extend(self.deps_of(&r));
                    refs.push(r);
                }
                let name = self.sig.rules[*r].name.clone();
                let n = self.cert.line(
                    format!(
                        "(step {} {name} ({}) {text})",
                        self.cert.steps,
                        refs.join(" ")
                    ),
                    deps,
                );
                // Only a judgment that depends on no hypothesis holds
                // everywhere later.
                if self.cert.deps[n].is_empty() {
                    self.cert.derived.insert(text, n);
                }
                Ok(n.to_string())
            }
        }
    }

    /// A step number for a reference; an instance of an earlier theorem
    /// becomes an `apply` step.
    fn as_step(&mut self, r: &str) -> usize {
        if let Ok(n) = r.parse() {
            return n;
        }
        let inner = &r[1..r.len() - 1];
        let (k, binds) = inner.split_once(' ').unwrap_or((inner, ""));
        self.cert.line(
            format!("(apply {} {k} ({binds}) ())", self.cert.steps),
            Vec::new(),
        )
    }

    fn prover(&self) -> Prover {
        Prover {
            sig: Rc::new(self.sig.clone()),
            binding: Vec::new(),
            var_sort: Vec::new(),
            trail: Vec::new(),
            facts: self.facts.clone(),
            hyps: Vec::new(),
            budget: 0,
            round: 2_000_000,
            max_depth: 1 << 14,
            cut: false,
        }
    }

    /// Search for a proof of a closed goal from hypotheses; returns a
    /// reference.
    fn search(&mut self, goal: &T, ctx: &[Hyp]) -> Result<Option<String>> {
        let mut pr = self.prover();
        pr.hyps = ctx.to_vec();
        if !ctx.is_empty() {
            // Hypothetical goals are tried often, under case analysis.
            pr.round = 20_000;
            pr.max_depth = 64;
        }
        match pr.prove(goal) {
            Some(p) => Ok(Some(self.emit(&pr, &p)?)),
            None => Ok(None),
        }
    }

    /// Search, then case analysis on plain hypotheses, newest first, up to
    /// `inv` levels deep.
    fn prove_goal(&mut self, goal: &T, ctx: &[Hyp], inv: u32) -> Result<Option<String>> {
        if let Some(r) = self.search(goal, ctx)? {
            return Ok(Some(r));
        }
        if inv == 0 {
            return Ok(None);
        }
        for k in (0..ctx.len()).rev() {
            if !ctx[k].premises.is_empty() || !ctx[k].general.is_empty() {
                continue;
            }
            let mark = self.mark();
            if let Some(n) = self.invert(k, goal, ctx, inv - 1)? {
                return Ok(Some(n.to_string()));
            }
            self.restore(mark);
        }
        Ok(None)
    }

    fn mark(&self) -> Mark {
        Mark(self.cert.proof.len(), self.cert.steps, self.sig.rigid.len())
    }

    /// Forget everything written since the mark.
    fn restore(&mut self, m: Mark) {
        self.cert.proof.truncate(m.0);
        self.cert.steps = m.1;
        self.cert.deps.truncate(m.1);
        self.cert.derived.retain(|_, n| *n < m.1);
        self.cert.hyps.retain(|n| *n < m.1);
        self.sig.rigid.truncate(m.2);
    }

    /// Declare a fresh eigenvariable in the proof.
    fn declare(&mut self, base: &str, sort: u32) -> u32 {
        let name = self.unique(base);
        let e = self.sig.rigid.len() as u32;
        let _ = writeln!(
            self.cert.proof,
            "(var {name} {})",
            self.sig.sorts[sort as usize]
        );
        self.sig.rigid.push((name, sort));
        e
    }

    /// Assume a hypothesis: plain, or a rule over its premises that
    /// generalizes the given names.
    fn hyp_line(&mut self, premises: &[T], concl: &T, general: &[u32]) -> Hyp {
        let n = self.cert.steps;
        let line = if premises.is_empty() && general.is_empty() {
            format!("(hyp {n} {})", self.text(concl))
        } else {
            let ps: Vec<String> = premises.iter().map(|p| self.text(p)).collect();
            let gs: Vec<String> = general
                .iter()
                .map(|&g| self.sig.rigid[g as usize].0.clone())
                .collect();
            format!(
                "(hyp {n} ({}) {} ({}))",
                ps.join(" "),
                self.text(concl),
                gs.join(" ")
            )
        };
        self.cert.line(line, vec![n]);
        self.cert.hyps.insert(n);
        Hyp {
            premises: premises.to_vec(),
            concl: concl.clone(),
            general: general.to_vec(),
            step: n,
        }
    }

    /// Case analysis on the plain hypothesis `ctx[k]`: one case per rule
    /// whose conclusion unifies with it, under the most general unifier.
    fn invert(&mut self, k: usize, goal: &T, ctx: &[Hyp], inv: u32) -> Result<Option<usize>> {
        let h = ctx[k].concl.clone();
        let T::A(pred, _) = &h else { return Ok(None) };
        let context: Vec<Hyp> = ctx
            .iter()
            .enumerate()
            .filter(|&(i, _)| i != k)
            .map(|(_, c)| c.clone())
            .collect();
        let mut cases = Vec::new();
        for r in 0..self.sig.rules.len() {
            let rule = self.sig.rules[r].clone();
            if !matches!(&rule.conclusion, Pat::A(p, _) if p == pred) {
                continue;
            }
            let mark = self.mark();
            let names: Vec<u32> = rule
                .sorts
                .iter()
                .enumerate()
                .map(|(i, &s)| self.declare(&format!("{}.{i}", rule.name), s))
                .collect();
            let env: Vec<T> = names.iter().map(|&e| T::E(e)).collect();
            let Some(theta) = unify_names(&h, &pat_inst(&rule.conclusion, &env)) else {
                self.restore(mark);
                continue;
            };
            let mut case_ctx = Vec::new();
            for p in &rule.premises {
                let t = subst_map(&pat_inst(p, &env), &theta);
                case_ctx.push(self.hyp_line(&[], &t, &[]));
            }
            // A rule hypothesis keeps its generalized names.
            for c in &context {
                let local: HashMap<u32, T> = theta
                    .iter()
                    .filter(|(v, _)| !c.general.contains(v))
                    .map(|(&v, t)| (v, t.clone()))
                    .collect();
                if local
                    .values()
                    .any(|t| c.general.iter().any(|&g| mentions(t, g)))
                {
                    return Ok(None);
                }
                let ps: Vec<T> = c.premises.iter().map(|p| subst_map(p, &local)).collect();
                let cj = subst_map(&c.concl, &local);
                case_ctx.push(self.hyp_line(&ps, &cj, &c.general));
            }
            let want = subst_map(goal, &theta);
            let Some(m) = self.prove_goal(&want, &case_ctx, inv)? else {
                return Ok(None);
            };
            let m = self.as_step(&m);
            let xs: Vec<String> = names
                .iter()
                .map(|&e| self.sig.rigid[e as usize].0.clone())
                .collect();
            cases.push(format!("({} {m} ({}))", rule.name, xs.join(" ")));
        }
        let mut deps: Vec<usize> = context.iter().map(|c| c.step).collect();
        deps.push(ctx[k].step);
        let cs: Vec<String> = context.iter().map(|c| c.step.to_string()).collect();
        let n = self.cert.line(
            format!(
                "(invert {} {} ({}) {} ({}))",
                self.cert.steps,
                ctx[k].step,
                cs.join(" "),
                self.text(goal),
                cases.join(" ")
            ),
            deps,
        );
        Ok(Some(n))
    }

    /// Structural induction on `x` for `hyps → concl`. With hypotheses,
    /// the induction hypothesis is a rule that generalizes the other names.
    fn induct(&mut self, x: u32, hyps: &[Hyp], concl: &T, inv: u32) -> Result<Option<usize>> {
        let mut motive = Vec::new();
        rigid_vars(concl, &mut motive);
        for h in hyps {
            rigid_vars(&h.concl, &mut motive);
        }
        if !motive.contains(&x) {
            return Ok(None);
        }
        let others: Vec<u32> = motive.iter().copied().filter(|&v| v != x).collect();
        let sort = self.sig.rigid[x as usize].1;
        let ctors: Vec<u32> = (0..self.sig.names.len() as u32)
            .filter(|&c| self.sig.output[c as usize] == Some(sort))
            .collect();
        let mut cases = Vec::new();
        for c in ctors {
            let mut ys = Vec::new();
            for (k, &s) in self.sig.inputs[c as usize].clone().iter().enumerate() {
                let base = format!(
                    "{}.{}{k}",
                    self.sig.rigid[x as usize].0, self.sig.names[c as usize]
                );
                ys.push((self.declare(&base, s), s));
            }
            let term = T::A(
                c,
                ys.iter().map(|&(e, _)| T::E(e)).collect::<Vec<_>>().into(),
            );
            let mut ctx = Vec::new();
            for h in hyps {
                ctx.push(self.hyp_line(&[], &subst_e(&h.concl, x, &term), &[]));
            }
            for &(e, s) in &ys {
                if s == sort {
                    let y = T::E(e);
                    let ps: Vec<T> = hyps.iter().map(|h| subst_e(&h.concl, x, &y)).collect();
                    let general = if hyps.is_empty() {
                        Vec::new()
                    } else {
                        others.clone()
                    };
                    ctx.push(self.hyp_line(&ps, &subst_e(concl, x, &y), &general));
                }
            }
            let goal = subst_e(concl, x, &term);
            let Some(r) = self.prove_goal(&goal, &ctx, inv)? else {
                return Ok(None);
            };
            let step = self.as_step(&r);
            let vars: Vec<String> = ys
                .iter()
                .map(|&(e, _)| self.sig.rigid[e as usize].0.clone())
                .collect();
            cases.push(if vars.is_empty() {
                format!("({step})")
            } else {
                format!("({step} {})", vars.join(" "))
            });
        }
        let text = self.text(concl);
        let xname = self.sig.rigid[x as usize].0.clone();
        let n = if hyps.is_empty() {
            self.cert.line(
                format!(
                    "(induct {} {xname} {text} ({}))",
                    self.cert.steps,
                    cases.join(" ")
                ),
                Vec::new(),
            )
        } else {
            let hs: Vec<String> = hyps.iter().map(|h| h.step.to_string()).collect();
            self.cert.line(
                format!(
                    "(induct {} {xname} ({}) {text} ({}))",
                    self.cert.steps,
                    hs.join(" "),
                    cases.join(" ")
                ),
                hyps.iter().map(|h| h.step).collect(),
            )
        };
        Ok(Some(n))
    }

    fn unique(&self, name: &str) -> String {
        let mut n = name.to_owned();
        while self.sig.rigid.iter().any(|(r, _)| *r == n) || self.sig.sym_ix.contains_key(&n) {
            n.push('\'');
        }
        n
    }

    fn goal(&mut self, name: &str, hyps: &[T], stmt: &T, r: &str) {
        let text = self.text(stmt);
        if hyps.is_empty() {
            let _ = writeln!(self.cert.goals, "(goal {name} {text})");
        } else {
            let hs: Vec<String> = hyps.iter().map(|h| self.text(h)).collect();
            let _ = writeln!(self.cert.goals, "(goal {name} ({}) {text})", hs.join(" "));
        }
        let _ = writeln!(self.cert.proof, "(result {name} {r})");
        self.goal_count += 1;
    }
}

/// How many case analyses deep a proof may go.
const MAX_INV: u32 = 2;

/// A position in the certificate to roll back to.
struct Mark(usize, usize, usize);

fn pat_inst(p: &Pat, env: &[T]) -> T {
    match p {
        Pat::Var(v) => env[*v].clone(),
        Pat::E(e) => T::E(*e),
        Pat::A(f, args) => T::A(
            *f,
            args.iter()
                .map(|a| pat_inst(a, env))
                .collect::<Vec<_>>()
                .into(),
        ),
    }
}

fn t_pat(t: &T) -> Pat {
    match t {
        T::V(_) => unreachable!("closed"),
        T::E(e) => Pat::E(*e),
        T::A(f, args) => Pat::A(*f, args.iter().map(t_pat).collect()),
    }
}

fn pat_t(p: &Pat) -> T {
    match p {
        Pat::Var(_) => unreachable!("statements have no variables"),
        Pat::E(e) => T::E(*e),
        Pat::A(f, args) => T::A(*f, args.iter().map(pat_t).collect::<Vec<_>>().into()),
    }
}

fn subst_e(t: &T, x: u32, by: &T) -> T {
    match t {
        T::E(e) if *e == x => by.clone(),
        T::A(f, args) => T::A(
            *f,
            args.iter()
                .map(|a| subst_e(a, x, by))
                .collect::<Vec<_>>()
                .into(),
        ),
        t => t.clone(),
    }
}

fn mentions(t: &T, x: u32) -> bool {
    match t {
        T::E(e) => *e == x,
        T::A(_, args) => args.iter().any(|a| mentions(a, x)),
        T::V(_) => false,
    }
}

/// The outcome of running a file.
pub struct Run {
    /// One line per `#eval`, `#check` and `theorem`.
    pub report: Vec<String>,
    pub theory: String,
    pub goals: String,
    pub proof: String,
    pub checked: schematic::Report,
}

/// Elaborate, evaluate and prove a source file, then check the resulting
/// certificate with the schematic checker.
pub fn run(src: &str) -> Result<Run> {
    let decls = parse(src)?;
    let mut s = Session {
        sig: Sig {
            sorts: Vec::new(),
            sort_ix: HashMap::new(),
            names: Vec::new(),
            sym_ix: HashMap::new(),
            inputs: Vec::new(),
            output: Vec::new(),
            defs: HashSet::new(),
            rules: Vec::new(),
            rigid: Vec::new(),
        },
        cert: Cert {
            goals: String::new(),
            proof: String::new(),
            steps: 0,
            derived: HashMap::new(),
            deps: Vec::new(),
            hyps: HashSet::new(),
        },
        facts: Vec::new(),
        report: Vec::new(),
        goal_count: 0,
    };
    // Declarations first, so that the theory is fixed before any proof.
    for (d, line) in &decls {
        let at = |e: String| format!("line {line}: {e}");
        match d {
            Decl::Sort(n) => {
                s.sig.fresh_name(n).map_err(at)?;
                s.sig.sort_ix.insert(n.clone(), s.sig.sorts.len() as u32);
                s.sig.sorts.push(n.clone());
            }
            Decl::Ctor(n, ins, out) => {
                let ins = ins
                    .iter()
                    .map(|x| s.sig.sort(x))
                    .collect::<Result<Vec<_>>>()
                    .map_err(at)?;
                let out = s.sig.sort(out).map_err(at)?;
                s.sig.add_sym(n, ins, Some(out)).map_err(at)?;
            }
            Decl::Pred(n, ins) => {
                let ins = ins
                    .iter()
                    .map(|x| s.sig.sort(x))
                    .collect::<Result<Vec<_>>>()
                    .map_err(at)?;
                s.sig.add_sym(n, ins, None).map_err(at)?;
            }
            Decl::Def(n, ins, out, _) => {
                let mut sorts = ins
                    .iter()
                    .map(|x| s.sig.sort(x))
                    .collect::<Result<Vec<_>>>()
                    .map_err(at)?;
                sorts.push(s.sig.sort(out).map_err(at)?);
                s.sig.add_sym(n, sorts, None).map_err(at)?;
                s.sig.defs.insert(n.clone());
            }
            _ => {}
        }
    }
    for (d, line) in &decls {
        let at = |e: String| format!("line {line}: {e}");
        match d {
            Decl::Rule(n, ps, c) => s.sig.rule(n.clone(), ps, c).map_err(at)?,
            Decl::Def(n, ins, _, clauses) => {
                for (i, (pats, rhs)) in clauses.iter().enumerate() {
                    if pats.len() != ins.len() {
                        return Err(at(format!("{n} takes {} arguments", ins.len())));
                    }
                    s.sig.clause(n, i + 1, pats, rhs).map_err(at)?;
                }
            }
            _ => {}
        }
    }
    let theory = s.sig.theory_text();
    let mut evals = 0;
    for (d, line) in &decls {
        let at = |e: String| format!("line {line}: {e}");
        match d {
            Decl::Eval(t) | Decl::Check(t) => {
                evals += 1;
                // A function call asks for its result.
                let query = match t {
                    Term::App(f, args)
                        if s.sig.defs.contains(f)
                            && args.len() + 1 == s.sig.inputs[s.sig.sym_ix[f] as usize].len() =>
                    {
                        let mut args = args.clone();
                        args.push(Term::Meta("result".into()));
                        Term::App(f.clone(), args)
                    }
                    t => t.clone(),
                };
                let mut vars = Vars {
                    names: Vec::new(),
                    sorts: Vec::new(),
                };
                let pat = s
                    .sig
                    .pattern(&query, None, &mut vars, &HashMap::new(), true)
                    .map_err(at)?;
                let mut pr = s.prover();
                let mut env = vec![None; vars.names.len()];
                let sorts: Vec<u32> = vars
                    .sorts
                    .iter()
                    .map(|x| x.ok_or_else(|| at("cannot tell the sort of a query variable".into())))
                    .collect::<Result<_>>()?;
                let goal = pr.inst(&pat, &mut env, &sorts, &[]);
                let Some(p) = pr.prove(&goal) else {
                    s.report.push(format!("line {line}: no derivation found"));
                    return Err(at("no derivation found".into()));
                };
                let closed = s.close(&pr, &goal).map_err(at)?;
                let r = s.emit(&pr, &p).map_err(at)?;
                let name = format!("eval.{evals}");
                s.goal(&name, &[], &closed, &r);
                let shown = match (&query, t) {
                    (Term::App(_, _), Term::App(f, args))
                        if s.sig.defs.contains(f)
                            && args.len() + 1 == s.sig.inputs[s.sig.sym_ix[f] as usize].len() =>
                    {
                        let T::A(_, xs) = &closed else { unreachable!() };
                        format!("{}  ⟹  {}", s.show_call(&closed), s.show(&xs[xs.len() - 1]))
                    }
                    _ => {
                        let answers: Vec<String> = vars
                            .names
                            .iter()
                            .zip(&env)
                            .filter(|(n, _)| n.starts_with('?'))
                            .map(|(n, v)| {
                                let v = v.as_ref().map_or_else(
                                    || "_".into(),
                                    |v| s.show(&s.close(&pr, v).unwrap_or(T::E(0))),
                                );
                                format!("{n} = {v}")
                            })
                            .collect();
                        if answers.is_empty() {
                            format!("{}  ✓", s.show(&closed))
                        } else {
                            format!("{}  with {}", s.show(&closed), answers.join(", "))
                        }
                    }
                };
                s.report.push(shown);
            }
            Decl::Theorem(name, binders, hyps, concl, tactic) => {
                let mut rigid = HashMap::new();
                let mut order = Vec::new();
                for (b, sort) in binders {
                    let sort = s.sig.sort(sort).map_err(at)?;
                    let var = s.unique(&format!("{name}.{b}"));
                    let e = s.sig.rigid.len() as u32;
                    s.sig.rigid.push((var.clone(), sort));
                    let _ = writeln!(s.cert.goals, "(var {var} {})", s.sig.sorts[sort as usize]);
                    rigid.insert(b.clone(), e);
                    order.push((b.clone(), e));
                }
                // A call nested in the statement becomes a hypothesis about
                // a fresh result: `add m (succ n) = succ (add m n)` is
                // `add m n r → add m (succ n) (succ r)`.
                let mut calls = Vec::new();
                let mut fresh = 0;
                let mut stmt = Vec::new();
                for h in hyps {
                    let h = s
                        .sig
                        .flatten_judgment(h, &mut calls, &mut fresh)
                        .map_err(at)?;
                    stmt.append(&mut calls);
                    stmt.push(h);
                }
                let concl = s
                    .sig
                    .flatten_judgment(concl, &mut calls, &mut fresh)
                    .map_err(at)?;
                stmt.append(&mut calls);
                let mut vars = Vars {
                    names: Vec::new(),
                    sorts: Vec::new(),
                };
                for j in stmt.iter().chain([&concl]) {
                    s.sig
                        .pattern(j, None, &mut vars, &rigid, true)
                        .map_err(at)?;
                }
                for (v, sort) in vars.names.iter().zip(&vars.sorts) {
                    let Some(k) = v.strip_prefix("result.") else {
                        return Err(at(format!("{v} is not bound; add it as `({v} : Sort)`")));
                    };
                    let sort = sort.ok_or_else(|| at(format!("cannot tell the sort of {v}")))?;
                    let var = s.unique(&format!("{name}.r{k}"));
                    let e = s.sig.rigid.len() as u32;
                    s.sig.rigid.push((var.clone(), sort));
                    let _ = writeln!(s.cert.goals, "(var {var} {})", s.sig.sorts[sort as usize]);
                    rigid.insert(v.clone(), e);
                    order.push((format!("r{k}"), e));
                }
                let mut vars = Vars {
                    names: Vec::new(),
                    sorts: Vec::new(),
                };
                let mut judgment = |j: &Term| s.sig.pattern(j, None, &mut vars, &rigid, true);
                let hyp_ts: Vec<T> = stmt
                    .iter()
                    .map(|j| judgment(j).map(|p| pat_t(&p)))
                    .collect::<Result<_>>()
                    .map_err(at)?;
                let pat = judgment(&concl).map_err(at)?;
                let goal = pat_t(&pat);
                let ctx: Vec<Hyp> = hyp_ts.iter().map(|h| s.hyp_line(&[], h, &[])).collect();
                let mut how = String::new();
                let result = match tactic {
                    Tactic::Induction(x) => {
                        let e = *rigid
                            .get(x)
                            .ok_or_else(|| at(format!("{x} is not a binder")))?;
                        how = format!("by induction {x}");
                        s.induct(e, &ctx, &goal, MAX_INV)
                            .map_err(at)?
                            .map(|n| n.to_string())
                    }
                    Tactic::Auto => match s.prove_goal(&goal, &ctx, MAX_INV).map_err(at)? {
                        Some(r) => {
                            how = "by auto".into();
                            Some(r)
                        }
                        None => {
                            let mut found = None;
                            for (b, e) in order.iter().map(|(b, e)| (b, *e)) {
                                let mark = s.mark();
                                if let Some(n) = s.induct(e, &ctx, &goal, MAX_INV).map_err(at)? {
                                    how = format!("by induction {b}");
                                    found = Some(n.to_string());
                                    break;
                                }
                                s.restore(mark);
                            }
                            found
                        }
                    },
                };
                let Some(r) = result else {
                    return Err(at(format!("could not prove {name}")));
                };
                s.goal(name, &hyp_ts, &goal, &r);
                // Later proofs may use the theorem, with the hypotheses
                // its proof needs as premises.
                if let Ok(step) = r.parse::<usize>() {
                    let used = s.cert.deps[step].clone();
                    s.facts.push(Fact {
                        stmt: pat.clone(),
                        premises: ctx
                            .iter()
                            .filter(|h| used.contains(&h.step))
                            .map(|h| t_pat(&h.concl))
                            .collect(),
                        names: order.iter().map(|&(_, e)| e).collect(),
                        step,
                    });
                }
                let mut shown: Vec<String> = hyp_ts.iter().map(|h| s.show(h)).collect();
                shown.push(s.show(&goal));
                s.report
                    .push(format!("theorem {name} : {}  ✓ ({how})", shown.join(" → ")));
            }
            _ => {}
        }
    }
    // A file with only declarations has nothing to check.
    let checked = if s.goal_count == 0 {
        schematic::Report::default()
    } else {
        schematic::check(&theory, &s.cert.goals, s.cert.proof.as_bytes())
            .map_err(|e| format!("the certificate was rejected: {e}"))?
    };
    Ok(Run {
        report: s.report,
        theory,
        goals: s.cert.goals,
        proof: s.cert.proof,
        checked,
    })
}

impl Session {
    /// `f a b` for a function judgment `f a b r`.
    fn show_call(&self, t: &T) -> String {
        let T::A(f, xs) = t else { return self.show(t) };
        let args: Vec<String> = xs[..xs.len() - 1]
            .iter()
            .map(|a| {
                let s = self.show(a);
                if s.contains(' ') { format!("({s})") } else { s }
            })
            .collect();
        format!("{} {}", self.sig.names[*f as usize], args.join(" "))
    }
}

/// Replace rigid names.
fn subst_names(t: &T, names: &[(u32, T)]) -> T {
    match t {
        T::E(e) => names
            .iter()
            .find(|(n, _)| n == e)
            .map_or(T::E(*e), |(_, u)| u.clone()),
        T::A(f, args) => T::A(
            *f,
            args.iter()
                .map(|a| subst_names(a, names))
                .collect::<Vec<_>>()
                .into(),
        ),
        t => t.clone(),
    }
}

fn subst_map(t: &T, map: &HashMap<u32, T>) -> T {
    match t {
        T::E(e) => map.get(e).cloned().unwrap_or(T::E(*e)),
        T::A(f, args) => T::A(
            *f,
            args.iter()
                .map(|a| subst_map(a, map))
                .collect::<Vec<_>>()
                .into(),
        ),
        t => t.clone(),
    }
}

fn same(a: &T, b: &T) -> bool {
    match (a, b) {
        (T::E(x), T::E(y)) => x == y,
        (T::V(x), T::V(y)) => x == y,
        (T::A(f, xs), T::A(g, ys)) => {
            f == g && xs.len() == ys.len() && xs.iter().zip(ys.iter()).all(|(x, y)| same(x, y))
        }
        _ => false,
    }
}

fn rigid_vars(t: &T, out: &mut Vec<u32>) {
    match t {
        T::E(e) => {
            if !out.contains(e) {
                out.push(*e);
            }
        }
        T::A(_, args) => args.iter().for_each(|a| rigid_vars(a, out)),
        T::V(_) => {}
    }
}

/// The most general unifier the schematic checker computes, with rigid
/// names as the unification variables; `src/schematic.rs` (`unify`) uses
/// the same order, so the certificate's case judgments match.
fn unify_names(a: &T, b: &T) -> Option<HashMap<u32, T>> {
    let mut theta: HashMap<u32, T> = HashMap::new();
    let mut work = vec![(a.clone(), b.clone())];
    while let Some((s, t)) = work.pop() {
        let s = subst_map(&s, &theta);
        let t = subst_map(&t, &theta);
        if same(&s, &t) {
            continue;
        }
        let (x, u) = match (&s, &t) {
            (T::E(x), _) => (*x, t.clone()),
            (_, T::E(y)) => (*y, s.clone()),
            (T::A(f, xs), T::A(g, ys)) => {
                if f != g || xs.len() != ys.len() {
                    return None;
                }
                work.extend(xs.iter().cloned().zip(ys.iter().cloned()));
                continue;
            }
            _ => return None,
        };
        if mentions(&u, x) {
            return None;
        }
        for v in theta.values_mut() {
            *v = subst_e(v, x, &u);
        }
        theta.insert(x, u);
    }
    Some(theta)
}
