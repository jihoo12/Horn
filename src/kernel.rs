//! Trusted algorithm: a many-sorted, first-order Horn proof checker.
//! No object-language substitution, reduction, typing, or equality algorithms.
//!
//! Ground terms and judgments are hash-consed: each distinct one is stored
//! once and named by an index. `Arena::make` is the only constructor and it
//! checks arity and argument sorts, so every index denotes a well-sorted
//! ground term, and two indices are equal exactly when their terms are
//! structurally equal (the table compares full nodes; hashes only choose
//! slots). Matching a rule therefore costs time proportional to the rule,
//! and memory is proportional to the number of distinct subterms.
use crate::lex::{Kind, Lexer, Token};
use crate::sexp::{MAX_DEPTH, Result, Sexp, parse};
use std::collections::{BTreeMap, HashMap};
use std::io::BufRead;

/// The output "sort" of predicates; never a declared sort index.
const PROP: u32 = u32::MAX;
const NONE: u32 = u32::MAX;

struct Symbol {
    inputs: Vec<u32>,
    output: u32,
}

enum Pattern {
    Var(usize),
    App(u32, Vec<Pattern>),
}

struct Rule {
    /// Schema variable names and sorts, indexed by `Pattern::Var`.
    vars: Vec<(String, u32)>,
    premises: Vec<Pattern>,
    conclusion: Pattern,
}

pub struct Theory {
    sorts: HashMap<String, u32>,
    constructors: HashMap<String, u32>,
    predicates: HashMap<String, u32>,
    symbols: Vec<Symbol>,
    rules: HashMap<String, Rule>,
}

fn name(x: &Sexp) -> Result<&str> {
    let s = x.atom()?;
    if s.starts_with('?') {
        return Err("declaration names cannot be variables".into());
    }
    Ok(s)
}

impl Theory {
    pub fn parse(source: &str) -> Result<Self> {
        let mut th = Self {
            sorts: HashMap::new(),
            constructors: HashMap::new(),
            predicates: HashMap::new(),
            symbols: Vec::new(),
            rules: HashMap::new(),
        };
        for form in parse(source)? {
            let xs = form.list()?;
            let tag = xs.first().ok_or("empty declaration")?.atom()?;
            match (tag, xs.len()) {
                ("sort", 2) => {
                    let id = th.sorts.len() as u32;
                    if th.sorts.insert(name(&xs[1])?.to_owned(), id).is_some() {
                        return Err("duplicate sort".into());
                    }
                }
                ("ctor", 4) | ("pred", 3) => {
                    let key = name(&xs[1])?.to_owned();
                    let inputs = xs[2]
                        .list()?
                        .iter()
                        .map(|s| th.sort(s))
                        .collect::<Result<_>>()?;
                    let (output, table) = if tag == "ctor" {
                        (th.sort(&xs[3])?, &mut th.constructors)
                    } else {
                        (PROP, &mut th.predicates)
                    };
                    if table.insert(key, th.symbols.len() as u32).is_some() {
                        return Err(format!("duplicate {tag}"));
                    }
                    th.symbols.push(Symbol { inputs, output });
                }
                ("rule", 4) => {
                    let mut vars = Vec::new();
                    let premises = xs[2]
                        .list()?
                        .iter()
                        .map(|j| th.pattern(j, PROP, &mut vars))
                        .collect::<Result<_>>()?;
                    let conclusion = th.pattern(&xs[3], PROP, &mut vars)?;
                    let rule = Rule {
                        vars,
                        premises,
                        conclusion,
                    };
                    if th.rules.insert(name(&xs[1])?.to_owned(), rule).is_some() {
                        return Err("duplicate rule".into());
                    }
                }
                _ => return Err(format!("invalid theory declaration: {form}")),
            }
        }
        Ok(th)
    }

    fn sort(&self, x: &Sexp) -> Result<u32> {
        let s = name(x)?;
        self.sorts
            .get(s)
            .copied()
            .ok_or_else(|| format!("unknown sort {s}"))
    }

    /// Compile a schema term of sort `sort`, or a judgment when `sort == PROP`.
    fn pattern(&self, x: &Sexp, sort: u32, vars: &mut Vec<(String, u32)>) -> Result<Pattern> {
        let (head, args) = match x {
            _ if sort == PROP => {
                let xs = x.list()?;
                let p = xs.first().ok_or("empty judgment")?.atom()?;
                let head = self.predicates.get(p);
                (
                    *head.ok_or_else(|| format!("unknown predicate {p}"))?,
                    &xs[1..],
                )
            }
            Sexp::Atom(v) if v.starts_with('?') => {
                if v.len() == 1 {
                    return Err(format!("invalid ground variable {v}"));
                }
                let i = match vars.iter().position(|(n, _)| n == v) {
                    Some(i) if vars[i].1 != sort => {
                        return Err(format!("variable {v} has conflicting sorts"));
                    }
                    Some(i) => i,
                    None => {
                        vars.push((v.clone(), sort));
                        vars.len() - 1
                    }
                };
                return Ok(Pattern::Var(i));
            }
            Sexp::Atom(c) => (self.constructor(c)?, &[][..]),
            Sexp::List(xs) => {
                let h = xs.first().ok_or("empty term")?.atom()?;
                if xs.len() == 1 {
                    return Err("nullary constructors must be atoms".into());
                }
                (self.constructor(h)?, &xs[1..])
            }
        };
        let symbol = &self.symbols[head as usize];
        if symbol.output != sort || symbol.inputs.len() != args.len() {
            return Err(format!("sort or arity mismatch: {x}"));
        }
        let args = args.iter().zip(&symbol.inputs);
        let args = args.map(|(a, &s)| self.pattern(a, s, vars));
        Ok(Pattern::App(head, args.collect::<Result<_>>()?))
    }

    fn constructor(&self, c: &str) -> Result<u32> {
        self.constructors
            .get(c)
            .copied()
            .ok_or_else(|| format!("unknown constructor {c}"))
    }

    pub fn check(&self, goals_source: &str, proof_source: &str) -> Result<Report> {
        self.check_reader(goals_source, proof_source.as_bytes())
    }

    /// Check a certificate read incrementally. Memory use is proportional to
    /// the number of steps and distinct subterms, not to the input size.
    pub fn check_reader(&self, goals_source: &str, proof: impl BufRead) -> Result<Report> {
        let mut ck = Checker {
            th: self,
            arena: Arena::new(),
            defs: HashMap::new(),
            stack: Vec::new(),
        };
        let mut goals = BTreeMap::new();
        let lx = &mut Lexer::new(goals_source.as_bytes());
        while lx.peek()?.is_some() {
            ck.open(lx, 0)?;
            if ck.atom(lx, 1)? != "goal" {
                return Err("expected (goal name judgment)".into());
            }
            let key = ck.atom(lx, 1)?;
            if key.starts_with('?') {
                return Err("declaration names cannot be variables".into());
            }
            let key = key.to_owned();
            let judgment = ck.judgment(lx, 1)?;
            ck.end(lx)?;
            if goals.insert(key, judgment).is_some() {
                return Err("duplicate goal".into());
            }
        }
        if goals.is_empty() {
            return Err("no expected goals".into());
        }
        let goal_count = goals.len();
        let mut steps = Vec::new();
        let lx = &mut Lexer::new(proof);
        while lx.peek()?.is_some() {
            ck.open(lx, 0)?;
            match ck.atom(lx, 1)? {
                "step" => ck.step(lx, &mut steps)?,
                "result" => {
                    let key = ck.atom(lx, 1)?;
                    let expected = goals
                        .remove(key)
                        .ok_or_else(|| format!("unknown or repeated result {key}"))?;
                    let fact = steps.get(ck.index(lx, 1)?).ok_or("unknown result step")?;
                    if *fact != expected {
                        return Err("result does not match the expected judgment".into());
                    }
                }
                "def" => {
                    let key = ck.atom(lx, 1)?;
                    if !key.starts_with('?') || key.len() == 1 {
                        return Err(format!("invalid abbreviation name {key}"));
                    }
                    let key = key.to_owned();
                    let term = ck.term(lx, 1)?;
                    if ck.defs.insert(key, term).is_some() {
                        return Err("duplicate abbreviation".into());
                    }
                }
                form => return Err(format!("invalid proof form: {form}")),
            }
            ck.end(lx)?;
        }
        if !goals.is_empty() {
            return Err(format!("missing results: {:?}", goals.keys()));
        }
        Ok(Report {
            steps: steps.len(),
            goals: goal_count,
            terms: ck.arena.len(),
            bytes: lx.bytes(),
        })
    }
}

/// Hash-consed nodes `[head, args...]` with a linear-probing index.
struct Arena {
    data: Vec<u32>,
    starts: Vec<usize>,
    table: Vec<u32>,
    bits: u32,
}

impl Arena {
    fn new() -> Self {
        Self {
            data: Vec::new(),
            starts: vec![0],
            table: vec![NONE; 1 << 10],
            bits: 10,
        }
    }

    fn len(&self) -> usize {
        self.starts.len() - 1
    }

    fn node(&self, id: u32) -> &[u32] {
        let i = id as usize;
        &self.data[self.starts[i]..self.starts[i + 1]]
    }

    fn slot(&self, key: &[u32]) -> usize {
        let mut h = 0u64;
        for &x in key {
            h = (h.rotate_left(5) ^ u64::from(x)).wrapping_mul(0x517c_c1b7_2722_0a95);
        }
        (h >> (64 - self.bits)) as usize
    }

    fn intern(&mut self, key: &[u32]) -> Result<u32> {
        if 2 * self.len() >= self.table.len() {
            self.bits += 1;
            self.table = vec![NONE; 1 << self.bits];
            for id in 0..self.len() as u32 {
                let mut i = self.slot(self.node(id));
                while self.table[i] != NONE {
                    i = (i + 1) & (self.table.len() - 1);
                }
                self.table[i] = id;
            }
        }
        let mut i = self.slot(key);
        loop {
            match self.table[i] {
                NONE => break,
                id if self.node(id) == key => return Ok(id),
                _ => i = (i + 1) & (self.table.len() - 1),
            }
        }
        let id = u32::try_from(self.len())
            .ok()
            .filter(|&id| id != NONE)
            .ok_or("too many distinct terms")?;
        self.data.extend_from_slice(key);
        self.starts.push(self.data.len());
        self.table[i] = id;
        Ok(id)
    }
}

struct Checker<'t> {
    th: &'t Theory,
    arena: Arena,
    defs: HashMap<String, u32>,
    /// Scratch space holding `[head, args...]` of nodes under construction.
    stack: Vec<u32>,
}

impl Checker<'_> {
    fn sort(&self, id: u32) -> u32 {
        self.th.symbols[self.arena.node(id)[0] as usize].output
    }

    /// Intern `stack[base..]` after checking arity and argument sorts.
    fn make(&mut self, base: usize) -> Result<u32> {
        let key = &self.stack[base..];
        let symbol = &self.th.symbols[key[0] as usize];
        if symbol.inputs.len() + 1 != key.len()
            || key[1..]
                .iter()
                .zip(&symbol.inputs)
                .any(|(&a, &s)| self.sort(a) != s)
        {
            return Err("sort or arity mismatch".into());
        }
        let id = self.arena.intern(key)?;
        self.stack.truncate(base);
        Ok(id)
    }

    fn item<'a, R: BufRead>(&self, lx: &'a mut Lexer<R>, depth: usize) -> Result<Token<'a>> {
        if depth > MAX_DEPTH {
            return Err("S-expression nesting exceeds 256".into());
        }
        match lx.token()?.ok_or("unexpected end of input")? {
            Token::Close => Err("unexpected closing parenthesis".into()),
            token => Ok(token),
        }
    }

    fn open<R: BufRead>(&self, lx: &mut Lexer<R>, depth: usize) -> Result<()> {
        match self.item(lx, depth)? {
            Token::Open => Ok(()),
            _ => Err("expected a list".into()),
        }
    }

    fn atom<'a, R: BufRead>(&self, lx: &'a mut Lexer<R>, depth: usize) -> Result<&'a str> {
        match self.item(lx, depth)? {
            Token::Atom(a) => Ok(a),
            _ => Err("expected an atom".into()),
        }
    }

    fn index<R: BufRead>(&self, lx: &mut Lexer<R>, depth: usize) -> Result<usize> {
        self.atom(lx, depth)?
            .parse()
            .map_err(|_| "expected a nonnegative step index".into())
    }

    fn end<R: BufRead>(&self, lx: &mut Lexer<R>) -> Result<()> {
        match lx.token()?.ok_or("unexpected end of input")? {
            Token::Close => Ok(()),
            _ => Err("too many elements in list".into()),
        }
    }

    /// Read the arguments of `head` at nesting `depth`, then the closing
    /// parenthesis. Only predicates may be written as one-element lists.
    fn args<R: BufRead>(&mut self, lx: &mut Lexer<R>, head: u32, depth: usize) -> Result<u32> {
        let base = self.stack.len();
        self.stack.push(head);
        while lx.peek()? != Some(Kind::Close) {
            let arg = self.term(lx, depth)?;
            self.stack.push(arg);
        }
        lx.token()?;
        if self.stack.len() == base + 1 && self.th.symbols[head as usize].output != PROP {
            return Err("nullary constructors must be atoms".into());
        }
        self.make(base)
    }

    /// A ground term of any sort; `?name` atoms refer to earlier `def` forms.
    fn term<R: BufRead>(&mut self, lx: &mut Lexer<R>, depth: usize) -> Result<u32> {
        let head = match self.item(lx, depth)? {
            Token::Atom(a) if a.starts_with('?') => {
                return self.defs.get(a).copied().ok_or_else(|| {
                    format!("invalid ground variable or undefined abbreviation {a}")
                });
            }
            Token::Atom(c) => {
                let head = self.th.constructor(c)?;
                let base = self.stack.len();
                self.stack.push(head);
                return self.make(base);
            }
            _ => match self.item(lx, depth + 1)? {
                Token::Atom(c) => self.th.constructor(c)?,
                _ => return Err("expected an atom".into()),
            },
        };
        self.args(lx, head, depth + 1)
    }

    fn judgment<R: BufRead>(&mut self, lx: &mut Lexer<R>, depth: usize) -> Result<u32> {
        self.open(lx, depth)?;
        let p = self.atom(lx, depth + 1)?;
        let head = self.th.predicates.get(p);
        let head = *head.ok_or_else(|| format!("unknown predicate {p}"))?;
        self.args(lx, head, depth + 1)
    }

    /// `(step N RULE (REFS...) ITEM...)`: each ITEM is either the stated
    /// conclusion or a binding `(?var TERM)`; without a stated conclusion it
    /// is built by instantiating the rule, so every variable must be bound.
    fn step<R: BufRead>(&mut self, lx: &mut Lexer<R>, steps: &mut Vec<u32>) -> Result<()> {
        let id = self.index(lx, 1)?;
        if id != steps.len() {
            return Err(format!("step {id}: expected next index {}", steps.len()));
        }
        let th = self.th;
        let rule_name = self.atom(lx, 1)?;
        let (rule_name, rule) = th
            .rules
            .get_key_value(rule_name)
            .ok_or_else(|| format!("unknown rule {rule_name}"))?;
        self.open(lx, 1)?;
        let mut refs = Vec::with_capacity(rule.premises.len());
        while lx.peek()? != Some(Kind::Close) {
            refs.push(self.index(lx, 2)?);
        }
        lx.token()?;
        if refs.len() != rule.premises.len() {
            return Err(format!("step {id}: wrong number of premises"));
        }
        let mut bindings = vec![NONE; rule.vars.len()];
        let mut stated = None;
        while lx.peek()? != Some(Kind::Close) {
            self.open(lx, 1)?;
            match self.atom(lx, 2)? {
                v if v.starts_with('?') => {
                    let i = rule.vars.iter().position(|(n, _)| n == v);
                    let i = i.ok_or_else(|| format!("step {id}: unknown variable {v}"))?;
                    let value = self.term(lx, 2)?;
                    self.end(lx)?;
                    if bindings[i] != NONE || self.sort(value) != rule.vars[i].1 {
                        return Err(format!("step {id}: invalid binding"));
                    }
                    bindings[i] = value;
                }
                p => {
                    let head = th.predicates.get(p);
                    let head = *head.ok_or_else(|| format!("unknown predicate {p}"))?;
                    let judgment = self.args(lx, head, 2)?;
                    if stated.replace(judgment).is_some() {
                        return Err(format!("step {id}: more than one conclusion"));
                    }
                }
            }
        }
        let arena = &self.arena;
        if let Some(j) = stated
            && !matches(arena, &rule.conclusion, j, &mut bindings)
        {
            return Err(format!("step {id} ({rule_name}): conclusion mismatch"));
        }
        for (pattern, &n) in rule.premises.iter().zip(&refs) {
            let fact = *steps
                .get(n)
                .ok_or_else(|| format!("step {id}: premise {n} is not an earlier step"))?;
            if !matches(arena, pattern, fact, &mut bindings) {
                return Err(format!("step {id} ({rule_name}): premise {n} mismatch"));
            }
        }
        let conclusion = match stated {
            Some(j) => j,
            None => self
                .build(&rule.conclusion, &bindings)
                .map_err(|e| format!("step {id} ({rule_name}): {e}"))?,
        };
        steps.push(conclusion);
        Ok(())
    }

    fn build(&mut self, pattern: &Pattern, bindings: &[u32]) -> Result<u32> {
        match pattern {
            Pattern::Var(v) if bindings[*v] == NONE => Err("unbound conclusion variable".into()),
            Pattern::Var(v) => Ok(bindings[*v]),
            Pattern::App(head, args) => {
                let base = self.stack.len();
                self.stack.push(*head);
                for a in args {
                    let id = self.build(a, bindings)?;
                    self.stack.push(id);
                }
                self.make(base)
            }
        }
    }
}

/// One consistent assignment must match every pattern; binding is by index.
fn matches(arena: &Arena, pattern: &Pattern, id: u32, bindings: &mut [u32]) -> bool {
    match pattern {
        Pattern::Var(v) if bindings[*v] == NONE => {
            bindings[*v] = id;
            true
        }
        Pattern::Var(v) => bindings[*v] == id,
        Pattern::App(head, args) => {
            let node = arena.node(id);
            node[0] == *head
                && node.len() == args.len() + 1
                && args
                    .iter()
                    .zip(&node[1..])
                    .all(|(p, &a)| matches(arena, p, a, bindings))
        }
    }
}

#[derive(Debug)]
pub struct Report {
    pub steps: usize,
    pub goals: usize,
    /// Distinct ground terms and judgments stored while checking.
    pub terms: usize,
    /// Certificate bytes read.
    pub bytes: u64,
}
