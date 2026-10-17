//! Research prototype, outside the trusted kernel: Horn certificates over
//! open judgments, with eigenvariables, hypotheses, and structural induction
//! over the term algebra.
//!
//! Additional forms, in the goals file or the certificate:
//!
//! ```text
//! (var NAME SORT)                     eigenvariable; not a constructor
//! (hyp N JUDGMENT)                    step N assumes JUDGMENT
//! (induct N X JUDGMENT (CASE...))     step N concludes JUDGMENT for all X
//! CASE   = (INDEX Y...)               one per constructor of X's sort
//! REF    = INDEX | (INDEX (VAR TERM)...)
//! ```
//!
//! A step's premise references are REFs: an earlier step, or an instance of
//! a hypothesis-free earlier step under a substitution of its variables.
//! `result` also takes a REF. Goals may contain variables.
//!
//! Meaning. A step with judgment J and hypothesis steps H is valid when for
//! every ground substitution of the variables of J and H, if every
//! hypothesis instance is derivable from the theory then so is the instance
//! of J. The checker keeps that invariant:
//!
//! - A rule step requires every premise instance and explicit binding to
//!   use only variables of its conclusion or hypotheses, so grounding those
//!   grounds the whole step. Without this an uninhabited sort would let a
//!   free variable stand for a term that does not exist.
//! - Instances are taken only of hypothesis-free steps.
//! - `induct` for X of sort S, where X occurs in J, with constructors c1..ck of S in theory order,
//!   requires case i to be a step concluding J[X := ci(Y...)] for distinct
//!   variables Y of ci's input sorts that do not occur in J. Its hypotheses
//!   must be `hyp` steps of the form J[X := Y] with Y among those variables
//!   of sort S. Every ground term of S is a finite constructor tree, so
//!   induction on it gives J for every instance; the result has no
//!   hypotheses.
//! - A result must be hypothesis-free and equal its goal exactly.
use crate::kernel;
use crate::lex::Lexer;
use crate::oracle::{Pat, Spec, Store};
use crate::sexp::{Result, Sexp, parse, read};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::io::{BufRead, Write};

const PROP: u32 = u32::MAX;

struct Fact {
    judgment: u32,
    /// Hypothesis steps this step depends on, sorted.
    hyps: Vec<u32>,
    is_hyp: bool,
}

struct Checker<'s> {
    spec: &'s Spec,
    /// Output sort of every symbol, then of every declared variable.
    output: Vec<u32>,
    vars: HashMap<String, u32>,
    arena: Store,
    /// Whether each arena node contains a variable.
    open: Vec<bool>,
    defs: HashMap<String, u32>,
    facts: Vec<Fact>,
}

#[derive(Debug, Default)]
pub struct Report {
    pub steps: usize,
    pub goals: usize,
    pub open_goals: usize,
    pub hypotheses: usize,
    pub inductions: usize,
    pub instances: usize,
}

pub fn check(theory: &str, goals: &str, proof: impl BufRead) -> Result<Report> {
    process(theory, goals, proof, None)
}

/// Check a schematic certificate, then write a ground goals file and an
/// ordinary certificate for the instance given by `bindings` (goal variable
/// name, ground term). Inductions are unfolded along the bound terms. The
/// output is untrusted; check it with the ground kernel.
pub fn instantiate(
    theory: &str,
    goals: &str,
    proof: impl BufRead,
    bindings: &[(String, String)],
    goals_out: &mut dyn Write,
    proof_out: &mut dyn Write,
) -> Result<Report> {
    process(theory, goals, proof, Some((bindings, goals_out, proof_out)))
}

type Out<'a> = (&'a [(String, String)], &'a mut dyn Write, &'a mut dyn Write);

fn process(theory: &str, goals: &str, proof: impl BufRead, out: Option<Out>) -> Result<Report> {
    // The kernel's parser validates declarations and rule sorts.
    kernel::Theory::parse(theory)?;
    let spec = Spec::parse(theory)?;
    let mut output = vec![PROP; spec.names.len()];
    for (sort, ctors) in spec.by_sort.iter().enumerate() {
        for &c in ctors {
            output[c as usize] = sort as u32;
        }
    }
    let mut ck = Checker {
        spec: &spec,
        output,
        vars: HashMap::new(),
        arena: Store::new(),
        open: Vec::new(),
        defs: HashMap::new(),
        facts: Vec::new(),
    };
    let mut report = Report::default();
    let mut expected = BTreeMap::new();
    let keep = out.is_some();
    let mut forms = Vec::new();
    let mut results = Vec::new();
    for form in parse(goals)? {
        let xs = form.list()?;
        match (xs.first().map(Sexp::atom).transpose()?, xs.len()) {
            (Some("var"), 3) => ck.declare(&xs[1], &xs[2])?,
            (Some("goal"), 3) => {
                let j = ck.judgment(&xs[2])?;
                report.open_goals += usize::from(ck.open[j as usize]);
                if expected.insert(xs[1].atom()?.to_owned(), j).is_some() {
                    return Err("duplicate goal".into());
                }
            }
            _ => return Err(format!("invalid goal form: {form}")),
        }
    }
    if expected.is_empty() {
        return Err("no expected goals".into());
    }
    report.goals = expected.len();
    let goal_list: Vec<(String, u32)> = expected.iter().map(|(k, &v)| (k.clone(), v)).collect();
    let lexer = &mut Lexer::new(proof);
    while lexer.peek()?.is_some() {
        let form = read(lexer, 0)?;
        let xs = form.list()?;
        let tag = xs.first().ok_or("empty form")?.atom()?;
        let id = || -> Result<usize> {
            let n = xs.get(1).ok_or("missing index")?.atom()?.parse::<usize>();
            n.map_err(|_| "expected a step index".into())
        };
        match (tag, xs.len()) {
            ("var", 3) => ck.declare(&xs[1], &xs[2])?,
            ("def", 3) => {
                let key = xs[1].atom()?;
                if !key.starts_with('?') || key.len() == 1 {
                    return Err(format!("invalid abbreviation name {key}"));
                }
                let term = ck.term(&xs[2], None)?;
                if ck.defs.insert(key.to_owned(), term).is_some() {
                    return Err("duplicate abbreviation".into());
                }
            }
            ("step" | "hyp" | "induct", _) if keep => forms.push(form.clone()),
            _ => {}
        }
        match (tag, xs.len()) {
            ("step", n) if n >= 4 => {
                ck.next(id()?)?;
                let instances = ck.step(&xs[2..])?;
                report.instances += instances;
            }
            ("hyp", 3) => {
                let n = ck.next(id()?)?;
                let judgment = ck.judgment(&xs[2])?;
                ck.facts.push(Fact {
                    judgment,
                    hyps: vec![n as u32],
                    is_hyp: true,
                });
                report.hypotheses += 1;
            }
            ("induct", 5) => {
                ck.next(id()?)?;
                ck.induct(&xs[2], &xs[3], &xs[4])?;
                report.inductions += 1;
            }
            ("result", 3) => {
                let key = xs[1].atom()?;
                if keep {
                    results.push((key.to_owned(), xs[2].clone()));
                }
                let goal = expected
                    .remove(key)
                    .ok_or_else(|| format!("unknown or repeated result {key}"))?;
                let (fact, hyps) = ck.reference(&xs[2])?;
                if !hyps.is_empty() {
                    return Err(format!("result {key} depends on hypotheses"));
                }
                if fact != goal {
                    return Err(format!("result {key} does not match its goal"));
                }
            }
            ("var" | "def", 3) => {}
            _ => return Err(format!("invalid proof form: {tag}")),
        }
    }
    if !expected.is_empty() {
        return Err(format!("missing results: {:?}", expected.keys()));
    }
    report.steps = ck.facts.len();
    if let Some((bindings, goals_out, proof_out)) = out {
        let mut sigma = HashMap::new();
        for (v, t) in bindings {
            let v = ck.var(&Sexp::Atom(v.clone()))?;
            let t = parse(t)?;
            let t = ck.term(t.first().ok_or("empty term")?, Some(ck.output[v as usize]))?;
            if ck.open[t as usize] {
                return Err("instance terms must be ground".into());
            }
            sigma.insert(v, t);
        }
        let mut g = Ground {
            ck: &mut ck,
            forms: &forms,
            table: HashMap::new(),
            defs: HashMap::new(),
            out: proof_out,
            steps: 0,
        };
        for (name, j) in &goal_list {
            let j = g.ck.substitute(*j, &sigma, &mut HashMap::new());
            if g.ck.open[j as usize] {
                return Err(format!("goal {name} has an unbound variable"));
            }
            writeln!(goals_out, "(goal {name} {})", g.tree(j)).map_err(|e| e.to_string())?;
        }
        for (name, r) in &results {
            let n = g.reference(r, &sigma)?;
            writeln!(g.out, "(result {name} {n})").map_err(|e| e.to_string())?;
        }
    }
    Ok(report)
}

/// Unfolds a checked schematic certificate into an ordinary one.
struct Ground<'c, 's> {
    ck: &'c mut Checker<'s>,
    forms: &'c [Sexp],
    /// Ground judgments already written, by arena node.
    table: HashMap<u32, u32>,
    defs: HashMap<u32, String>,
    out: &'c mut dyn Write,
    steps: u32,
}

impl Ground<'_, '_> {
    fn tree(&self, id: u32) -> String {
        let node = self.ck.arena.node(id);
        let name = &self.ck.spec.names[node[0] as usize];
        if node.len() == 1 && self.ck.output[node[0] as usize] != PROP {
            return name.clone();
        }
        let args: Vec<String> = node[1..].iter().map(|&a| self.tree(a)).collect();
        format!(
            "({name}{}{})",
            if args.is_empty() { "" } else { " " },
            args.join(" ")
        )
    }

    fn term(&mut self, id: u32) -> Result<String> {
        let node = self.ck.arena.node(id).to_vec();
        if node.len() == 1 {
            return Ok(self.ck.spec.names[node[0] as usize].clone());
        }
        if let Some(d) = self.defs.get(&id) {
            return Ok(d.clone());
        }
        let mut args = Vec::new();
        for &a in &node[1..] {
            args.push(self.term(a)?);
        }
        let name = format!("?g{}", self.defs.len());
        let head = &self.ck.spec.names[node[0] as usize];
        writeln!(self.out, "(def {name} ({head} {}))", args.join(" "))
            .map_err(|e| e.to_string())?;
        self.defs.insert(id, name.clone());
        Ok(name)
    }

    fn reference(&mut self, x: &Sexp, sigma: &HashMap<u32, u32>) -> Result<u32> {
        let index = |x: &Sexp| -> Result<usize> {
            x.atom()?
                .parse()
                .map_err(|_| "expected a step index".into())
        };
        match x {
            Sexp::Atom(_) => self.derive(index(x)?, sigma),
            Sexp::List(xs) => {
                let mut inner = sigma.clone();
                for b in &xs[1..] {
                    let ys = b.list()?;
                    let v = self.ck.var(&ys[0])?;
                    let t = self.ck.term(&ys[1], None)?;
                    inner.insert(v, self.ck.substitute(t, sigma, &mut HashMap::new()));
                }
                self.derive(index(&xs[0])?, &inner)
            }
        }
    }

    fn derive(&mut self, k: usize, sigma: &HashMap<u32, u32>) -> Result<u32> {
        let j = self.ck.facts[k].judgment;
        let j = self.ck.substitute(j, sigma, &mut HashMap::new());
        if self.ck.open[j as usize] {
            return Err(format!("step {k}: instance is not ground"));
        }
        if let Some(&n) = self.table.get(&j) {
            return Ok(n);
        }
        let forms = self.forms;
        let xs = forms[k].list()?;
        let n = match xs[0].atom()? {
            "step" => {
                let mut refs = Vec::new();
                for r in xs[3].list()? {
                    refs.push(self.reference(r, sigma)?.to_string());
                }
                let mut judgment =
                    vec![self.ck.spec.names[self.ck.arena.node(j)[0] as usize].clone()];
                let args = self.ck.arena.node(j)[1..].to_vec();
                for a in args {
                    judgment.push(self.term(a)?);
                }
                let n = self.steps;
                writeln!(
                    self.out,
                    "(step {n} {} ({}) ({}))",
                    xs[2].atom()?,
                    refs.join(" "),
                    judgment.join(" ")
                )
                .map_err(|e| e.to_string())?;
                self.steps += 1;
                n
            }
            "induct" => {
                let x = self.ck.var(&xs[2])?;
                let t = sigma.get(&x).copied().ok_or("induction variable unbound")?;
                let node = self.ck.arena.node(t).to_vec();
                let sort = self.ck.output[x as usize];
                let i = self.ck.spec.by_sort[sort as usize]
                    .iter()
                    .position(|&c| c == node[0])
                    .ok_or("induction on a term of another sort")?;
                let case = xs[4].list()?[i].list()?;
                let mut inner = sigma.clone();
                for (y, &a) in case[1..].iter().zip(&node[1..]) {
                    let y = self.ck.var(y)?;
                    if self.ck.output[y as usize] == sort {
                        let mut smaller = sigma.clone();
                        smaller.insert(x, a);
                        self.derive(k, &smaller)?;
                    }
                    inner.insert(y, a);
                }
                let m = case[0].atom()?.parse().map_err(|_| "bad case index")?;
                self.derive(m, &inner)?
            }
            _ => {
                return Err(format!(
                    "step {k}: hypothesis instance was not derived first"
                ));
            }
        };
        self.table.insert(j, n);
        Ok(n)
    }
}

impl Checker<'_> {
    fn next(&self, n: usize) -> Result<usize> {
        if n != self.facts.len() {
            return Err(format!(
                "step {n}: expected next index {}",
                self.facts.len()
            ));
        }
        Ok(n)
    }

    fn declare(&mut self, name: &Sexp, sort: &Sexp) -> Result<()> {
        let name = name.atom()?;
        let sort = sort.atom()?;
        let sort = *self
            .spec
            .sorts
            .get(sort)
            .ok_or_else(|| format!("unknown sort {sort}"))?;
        if name.starts_with('?')
            || self.spec.ctors.contains_key(name)
            || self.spec.preds.contains_key(name)
            || self.vars.contains_key(name)
        {
            return Err(format!("invalid or duplicate variable {name}"));
        }
        self.vars.insert(name.to_owned(), self.output.len() as u32);
        self.output.push(sort);
        Ok(())
    }

    fn is_var(&self, head: u32) -> bool {
        head as usize >= self.spec.names.len()
    }

    fn inputs(&self, head: u32) -> &[u32] {
        if self.is_var(head) {
            &[]
        } else {
            &self.spec.inputs[head as usize]
        }
    }

    fn sort(&self, id: u32) -> u32 {
        self.output[self.arena.node(id)[0] as usize]
    }

    /// Intern a node after checking arity and argument sorts.
    fn make(&mut self, key: &[u32]) -> Result<u32> {
        let inputs = self.inputs(key[0]);
        if inputs.len() + 1 != key.len()
            || key[1..]
                .iter()
                .zip(inputs)
                .any(|(&a, &s)| self.sort(a) != s)
        {
            return Err("sort or arity mismatch".into());
        }
        let id = self.arena.intern(key);
        if id as usize == self.open.len() {
            let open = self.is_var(key[0]) || key[1..].iter().any(|&a| self.open[a as usize]);
            self.open.push(open);
        }
        Ok(id)
    }

    /// A term of the given sort (any sort when `None`); judgments use
    /// `judgment`.
    fn term(&mut self, x: &Sexp, sort: Option<u32>) -> Result<u32> {
        let id = match x {
            Sexp::Atom(a) if a.starts_with('?') => *self
                .defs
                .get(a)
                .ok_or_else(|| format!("undefined abbreviation {a}"))?,
            Sexp::Atom(a) => {
                let head = match self.vars.get(a) {
                    Some(&v) => v,
                    None => *self
                        .spec
                        .ctors
                        .get(a)
                        .ok_or_else(|| format!("unknown constructor {a}"))?,
                };
                self.make(&[head])?
            }
            Sexp::List(xs) => {
                let h = xs.first().ok_or("empty term")?.atom()?;
                let head = *self
                    .spec
                    .ctors
                    .get(h)
                    .ok_or_else(|| format!("unknown constructor {h}"))?;
                if xs.len() == 1 {
                    return Err("nullary constructors must be atoms".into());
                }
                let mut key = vec![head];
                for a in &xs[1..] {
                    key.push(self.term(a, None)?);
                }
                self.make(&key)?
            }
        };
        if sort.is_some_and(|s| self.sort(id) != s) || self.sort(id) == PROP {
            return Err(format!("ill-sorted term {x}"));
        }
        Ok(id)
    }

    fn judgment(&mut self, x: &Sexp) -> Result<u32> {
        let xs = x.list()?;
        let p = xs.first().ok_or("empty judgment")?.atom()?;
        let head = *self
            .spec
            .preds
            .get(p)
            .ok_or_else(|| format!("unknown predicate {p}"))?;
        let mut key = vec![head];
        for a in &xs[1..] {
            key.push(self.term(a, None)?);
        }
        self.make(&key)
    }

    fn var(&self, x: &Sexp) -> Result<u32> {
        let a = x.atom()?;
        self.vars
            .get(a)
            .copied()
            .ok_or_else(|| format!("unknown variable {a}"))
    }

    fn substitute(
        &mut self,
        id: u32,
        map: &HashMap<u32, u32>,
        memo: &mut HashMap<u32, u32>,
    ) -> u32 {
        if !self.open[id as usize] {
            return id;
        }
        if let Some(&r) = memo.get(&id) {
            return r;
        }
        let node = self.arena.node(id).to_vec();
        let r = if node.len() == 1 {
            map.get(&node[0]).copied().unwrap_or(id)
        } else {
            let mut key = vec![node[0]];
            for &a in &node[1..] {
                key.push(self.substitute(a, map, memo));
            }
            // Substituting well-sorted terms for variables of the same sort
            // preserves sorts.
            self.make(&key).expect("substitution preserves sorts")
        };
        memo.insert(id, r);
        r
    }

    fn variables(&self, id: u32, out: &mut BTreeSet<u32>) {
        if !self.open[id as usize] {
            return;
        }
        let node = self.arena.node(id);
        if node.len() == 1 {
            out.insert(node[0]);
        }
        for &a in &node[1..] {
            self.variables(a, out);
        }
    }

    /// A premise or result reference: the judgment and its hypotheses.
    fn reference(&mut self, x: &Sexp) -> Result<(u32, Vec<u32>)> {
        let index = |x: &Sexp| -> Result<usize> {
            x.atom()?
                .parse()
                .map_err(|_| "expected a step index".into())
        };
        match x {
            Sexp::Atom(_) => {
                let f = self
                    .facts
                    .get(index(x)?)
                    .ok_or("reference to a later step")?;
                Ok((f.judgment, f.hyps.clone()))
            }
            Sexp::List(xs) => {
                let n = index(xs.first().ok_or("empty reference")?)?;
                let f = self.facts.get(n).ok_or("reference to a later step")?;
                if !f.hyps.is_empty() {
                    return Err(format!("instance of step {n}, which has hypotheses"));
                }
                let judgment = f.judgment;
                let mut map = HashMap::new();
                for b in &xs[1..] {
                    let ys = b.list()?;
                    if ys.len() != 2 {
                        return Err("expected (VAR TERM)".into());
                    }
                    let v = self.var(&ys[0])?;
                    let t = self.term(&ys[1], Some(self.output[v as usize]))?;
                    if map.insert(v, t).is_some() {
                        return Err("variable substituted twice".into());
                    }
                }
                Ok((
                    self.substitute(judgment, &map, &mut HashMap::new()),
                    Vec::new(),
                ))
            }
        }
    }

    fn matches(&self, pattern: &Pat, id: u32, bindings: &mut [u32]) -> bool {
        match pattern {
            Pat::Var(v) if bindings[*v] == u32::MAX => {
                bindings[*v] = id;
                true
            }
            Pat::Var(v) => bindings[*v] == id,
            Pat::App(head, args) => {
                let node = self.arena.node(id);
                node[0] == *head
                    && node.len() == args.len() + 1
                    && args
                        .iter()
                        .zip(&node[1..])
                        .all(|(p, &a)| self.matches(p, a, bindings))
            }
        }
    }

    fn build(&mut self, pattern: &Pat, bindings: &[u32]) -> Result<u32> {
        match pattern {
            Pat::Var(v) if bindings[*v] == u32::MAX => Err("unbound conclusion variable".into()),
            Pat::Var(v) => Ok(bindings[*v]),
            Pat::App(head, args) => {
                let mut key = vec![*head];
                for a in args {
                    key.push(self.build(a, bindings)?);
                }
                self.make(&key)
            }
        }
    }

    /// `RULE (REF...) ITEM...`; returns the number of instance references.
    fn step(&mut self, xs: &[Sexp]) -> Result<usize> {
        let spec = self.spec;
        let n = self.facts.len();
        let r = spec.rule(xs[0].atom()?)?;
        let rule = &spec.rules[r as usize];
        let refs = xs[1].list()?;
        if refs.len() != rule.premises.len() {
            return Err(format!("step {n}: wrong number of premises"));
        }
        let mut premises = Vec::new();
        let mut hyps = BTreeSet::new();
        let mut instances = 0;
        for x in refs {
            let (j, h) = self.reference(x)?;
            instances += usize::from(matches!(x, Sexp::List(_)));
            premises.push(j);
            hyps.extend(h);
        }
        let mut bindings = vec![u32::MAX; rule.vars.len()];
        let mut bound = Vec::new();
        let mut stated = None;
        for item in &xs[2..] {
            let ys = item.list()?;
            let head = ys.first().ok_or("empty item")?.atom()?;
            if head.starts_with('?') && ys.len() == 2 {
                let i = rule.vars.iter().position(|(v, _)| v == head);
                let i = i.ok_or_else(|| format!("step {n}: unknown variable {head}"))?;
                let value = self.term(&ys[1], Some(rule.vars[i].1))?;
                if bindings[i] != u32::MAX {
                    return Err(format!("step {n}: invalid binding"));
                }
                bindings[i] = value;
                bound.push(value);
            } else if stated.replace(self.judgment(item)?).is_some() {
                return Err(format!("step {n}: more than one conclusion"));
            }
        }
        if let Some(j) = stated
            && !self.matches(&rule.conclusion, j, &mut bindings)
        {
            return Err(format!("step {n} ({}): conclusion mismatch", rule.name));
        }
        for (p, &j) in rule.premises.iter().zip(&premises) {
            if !self.matches(p, j, &mut bindings) {
                return Err(format!("step {n} ({}): premise mismatch", rule.name));
            }
        }
        let judgment = match stated {
            Some(j) => j,
            None => self.build(&rule.conclusion, &bindings)?,
        };
        let open = premises
            .iter()
            .chain(&bound)
            .any(|&t| self.open[t as usize]);
        if open {
            let mut allowed = BTreeSet::new();
            self.variables(judgment, &mut allowed);
            for &h in &hyps {
                self.variables(self.facts[h as usize].judgment, &mut allowed);
            }
            for &t in premises.iter().chain(&bound) {
                let mut used = BTreeSet::new();
                self.variables(t, &mut used);
                if !used.is_subset(&allowed) {
                    return Err(format!(
                        "step {n} ({}): premise variable absent from the conclusion",
                        rule.name
                    ));
                }
            }
        }
        self.facts.push(Fact {
            judgment,
            hyps: hyps.into_iter().collect(),
            is_hyp: false,
        });
        Ok(instances)
    }

    fn induct(&mut self, x: &Sexp, j: &Sexp, cases: &Sexp) -> Result<()> {
        let n = self.facts.len();
        let x = self.var(x)?;
        let judgment = self.judgment(j)?;
        let sort = self.output[x as usize];
        let ctors = self.spec.by_sort[sort as usize].clone();
        let cases = cases.list()?;
        if cases.len() != ctors.len() {
            return Err(format!("step {n}: expected {} cases", ctors.len()));
        }
        let mut in_j = BTreeSet::new();
        self.variables(judgment, &mut in_j);
        // Otherwise, for a sort whose every constructor is recursive (a sort
        // without ground terms), each case could be its own hypothesis, and
        // the conclusion would not keep the vacuous quantifier.
        if !in_j.contains(&x) {
            return Err(format!(
                "step {n}: the induction variable must occur in the judgment"
            ));
        }
        for (case, &c) in cases.iter().zip(&ctors) {
            let ys = case.list()?;
            let m = ys.first().ok_or("empty case")?.atom()?.parse::<usize>();
            let m = m.map_err(|_| "expected a step index")?;
            let inputs = self.spec.inputs[c as usize].clone();
            if ys.len() != inputs.len() + 1 {
                return Err(format!(
                    "step {n}: case variables do not match the constructor"
                ));
            }
            let mut fresh = Vec::new();
            for (y, &s) in ys[1..].iter().zip(&inputs) {
                let v = self.var(y)?;
                if self.output[v as usize] != s || in_j.contains(&v) || fresh.contains(&v) {
                    return Err(format!("step {n}: invalid case variable {y}"));
                }
                fresh.push(v);
            }
            let mut key = vec![c];
            for &v in &fresh {
                key.push(self.make(&[v])?);
            }
            let term = self.make(&key)?;
            let want = self.substitute(judgment, &HashMap::from([(x, term)]), &mut HashMap::new());
            let mut ihs = Vec::new();
            for (&v, &s) in fresh.iter().zip(&inputs) {
                if s == sort {
                    let y = self.make(&[v])?;
                    ihs.push(self.substitute(
                        judgment,
                        &HashMap::from([(x, y)]),
                        &mut HashMap::new(),
                    ));
                }
            }
            let f = self.facts.get(m).ok_or("case refers to a later step")?;
            if f.judgment != want {
                return Err(format!("step {n}: case {m} proves the wrong judgment"));
            }
            for &h in &f.hyps {
                let h = &self.facts[h as usize];
                if !h.is_hyp || !ihs.contains(&h.judgment) {
                    return Err(format!(
                        "step {n}: case {m} uses a hypothesis that is not an induction hypothesis"
                    ));
                }
            }
        }
        self.facts.push(Fact {
            judgment,
            hyps: Vec::new(),
            is_hyp: false,
        });
        Ok(())
    }
}
