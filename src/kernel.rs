//! Trusted algorithm: a many-sorted, first-order Horn proof checker.
//! No object-language substitution, reduction, typing, or equality algorithms.
use crate::sexp::{Result, Sexp, parse};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug)]
struct Constructor {
    inputs: Vec<String>,
    output: String,
}

#[derive(Clone, Debug)]
struct Rule {
    premises: Vec<Sexp>,
    conclusion: Sexp,
}

pub struct Theory {
    sorts: BTreeSet<String>,
    constructors: BTreeMap<String, Constructor>,
    predicates: BTreeMap<String, Vec<String>>,
    rules: BTreeMap<String, Rule>,
}

fn name(x: &Sexp) -> Result<String> {
    let s = x.atom()?;
    if s.starts_with('?') {
        return Err("declaration names cannot be variables".into());
    }
    Ok(s.to_owned())
}

fn names(x: &Sexp) -> Result<Vec<String>> {
    x.list()?.iter().map(name).collect()
}

impl Theory {
    pub fn parse(source: &str) -> Result<Self> {
        let mut th = Self {
            sorts: BTreeSet::new(),
            constructors: BTreeMap::new(),
            predicates: BTreeMap::new(),
            rules: BTreeMap::new(),
        };
        for form in parse(source)? {
            let xs = form.list()?;
            let tag = xs.first().ok_or("empty declaration")?.atom()?;
            match (tag, xs.len()) {
                ("sort", 2) => {
                    if !th.sorts.insert(name(&xs[1])?) {
                        return Err("duplicate sort".into());
                    }
                }
                ("ctor", 4) => {
                    let key = name(&xs[1])?;
                    let ctor = Constructor {
                        inputs: names(&xs[2])?,
                        output: name(&xs[3])?,
                    };
                    for s in ctor.inputs.iter().chain(std::iter::once(&ctor.output)) {
                        if !th.sorts.contains(s) {
                            return Err(format!("unknown sort {s}"));
                        }
                    }
                    if th.constructors.insert(key, ctor).is_some() {
                        return Err("duplicate constructor".into());
                    }
                }
                ("pred", 3) => {
                    let args = names(&xs[2])?;
                    for s in &args {
                        if !th.sorts.contains(s) {
                            return Err(format!("unknown sort {s}"));
                        }
                    }
                    if th.predicates.insert(name(&xs[1])?, args).is_some() {
                        return Err("duplicate predicate".into());
                    }
                }
                ("rule", 4) => {
                    let rule = Rule {
                        premises: xs[2].list()?.to_vec(),
                        conclusion: xs[3].clone(),
                    };
                    let mut variables = BTreeMap::new();
                    for j in rule
                        .premises
                        .iter()
                        .chain(std::iter::once(&rule.conclusion))
                    {
                        th.judgment(j, true, &mut variables)?;
                    }
                    if th.rules.insert(name(&xs[1])?, rule).is_some() {
                        return Err("duplicate rule".into());
                    }
                }
                _ => return Err(format!("invalid theory declaration: {form}")),
            }
        }
        Ok(th)
    }

    fn term(
        &self,
        t: &Sexp,
        sort: &str,
        schema: bool,
        vars: &mut BTreeMap<String, String>,
    ) -> Result<()> {
        if let Sexp::Atom(v) = t
            && v.starts_with('?')
        {
            if !schema || v.len() == 1 {
                return Err(format!("invalid ground variable {v}"));
            }
            if let Some(previous) = vars.insert(v.clone(), sort.to_owned())
                && previous != sort
            {
                return Err(format!("variable {v} has conflicting sorts"));
            }
            return Ok(());
        }
        let (head, args) = match t {
            Sexp::Atom(s) => (s.as_str(), &[][..]),
            Sexp::List(xs) => {
                let h = xs.first().ok_or("empty term")?.atom()?;
                if xs.len() == 1 {
                    return Err("nullary constructors must be atoms".into());
                }
                (h, &xs[1..])
            }
        };
        let ctor = self
            .constructors
            .get(head)
            .ok_or_else(|| format!("unknown constructor {head}"))?;
        if ctor.output != sort || ctor.inputs.len() != args.len() {
            return Err(format!("sort or arity mismatch: {t}, expected {sort}"));
        }
        for (a, s) in args.iter().zip(&ctor.inputs) {
            self.term(a, s, schema, vars)?;
        }
        Ok(())
    }

    fn judgment(&self, j: &Sexp, schema: bool, vars: &mut BTreeMap<String, String>) -> Result<()> {
        let xs = j.list()?;
        let p = xs.first().ok_or("empty judgment")?.atom()?;
        let sorts = self
            .predicates
            .get(p)
            .ok_or_else(|| format!("unknown predicate {p}"))?;
        if sorts.len() + 1 != xs.len() {
            return Err(format!("predicate arity mismatch: {j}"));
        }
        for (arg, sort) in xs[1..].iter().zip(sorts) {
            self.term(arg, sort, schema, vars)?;
        }
        Ok(())
    }

    pub fn check(&self, goals_source: &str, proof_source: &str) -> Result<Report> {
        let mut goals = BTreeMap::new();
        for form in parse(goals_source)? {
            let xs = form.list()?;
            if xs.len() != 3 || xs[0].atom()? != "goal" {
                return Err("expected (goal name judgment)".into());
            }
            self.judgment(&xs[2], false, &mut BTreeMap::new())?;
            if goals.insert(name(&xs[1])?, xs[2].clone()).is_some() {
                return Err("duplicate goal".into());
            }
        }
        if goals.is_empty() {
            return Err("no expected goals".into());
        }
        let goal_count = goals.len();
        let mut steps: Vec<Sexp> = Vec::new();
        for form in parse(proof_source)? {
            let xs = form.list()?;
            match (xs.first().ok_or("empty proof form")?.atom()?, xs.len()) {
                ("step", 5) => {
                    let id = index(&xs[1])?;
                    if id != steps.len() {
                        return Err(format!("step {id}: expected next index {}", steps.len()));
                    }
                    let rule_name = xs[2].atom()?;
                    let rule = self
                        .rules
                        .get(rule_name)
                        .ok_or_else(|| format!("unknown rule {rule_name}"))?;
                    let refs = xs[3].list()?;
                    if refs.len() != rule.premises.len() {
                        return Err(format!("step {id}: wrong number of premises"));
                    }
                    self.judgment(&xs[4], false, &mut BTreeMap::new())?;
                    let mut bindings = BTreeMap::new();
                    match_schema(&rule.conclusion, &xs[4], &mut bindings)
                        .map_err(|e| format!("step {id} ({rule_name}): {e}"))?;
                    for (pattern, reference) in rule.premises.iter().zip(refs) {
                        let n = index(reference)?;
                        let fact = steps.get(n).ok_or_else(|| {
                            format!("step {id}: premise {n} is not an earlier step")
                        })?;
                        match_schema(pattern, fact, &mut bindings)
                            .map_err(|e| format!("step {id} ({rule_name}), premise {n}: {e}"))?;
                    }
                    steps.push(xs[4].clone());
                }
                ("result", 3) => {
                    let key = xs[1].atom()?;
                    let expected = goals
                        .remove(key)
                        .ok_or_else(|| format!("unknown or repeated result {key}"))?;
                    let fact = steps.get(index(&xs[2])?).ok_or("unknown result step")?;
                    if *fact != expected {
                        return Err(format!("result {key} does not match the expected judgment"));
                    }
                }
                _ => return Err(format!("invalid proof form: {form}")),
            }
        }
        if !goals.is_empty() {
            return Err(format!("missing results: {:?}", goals.keys()));
        }
        Ok(Report {
            steps: steps.len(),
            goals: goal_count,
        })
    }
}

fn index(x: &Sexp) -> Result<usize> {
    x.atom()?
        .parse()
        .map_err(|_| "expected a nonnegative step index".into())
}

fn match_schema(
    pattern: &Sexp,
    ground: &Sexp,
    bindings: &mut BTreeMap<String, Sexp>,
) -> Result<()> {
    match (pattern, ground) {
        (Sexp::Atom(v), _) if v.starts_with('?') => {
            if let Some(previous) = bindings.get(v) {
                if previous != ground {
                    return Err(format!("inconsistent substitution for {v}"));
                }
            } else {
                bindings.insert(v.clone(), ground.clone());
            }
            Ok(())
        }
        (Sexp::Atom(a), Sexp::Atom(b)) if a == b => Ok(()),
        (Sexp::List(ps), Sexp::List(gs)) if ps.len() == gs.len() => {
            for (p, g) in ps.iter().zip(gs) {
                match_schema(p, g, bindings)?;
            }
            Ok(())
        }
        _ => Err(format!("schema mismatch: {pattern} versus {ground}")),
    }
}

#[derive(Debug)]
pub struct Report {
    pub steps: usize,
    pub goals: usize,
}
