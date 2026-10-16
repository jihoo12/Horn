//! Untrusted certificate compressor; its output is checked like any other
//! certificate and nothing here is part of the trusted boundary.
//!
//! The output uses the compact forms of the certificate language: a step
//! omits its conclusion and binds only the rule variables that do not occur
//! in premises, steps proving an already proved judgment are replaced by the
//! earlier step, steps no result depends on are dropped, and every repeated
//! compound subterm of a binding is written once as `(def ?name TERM)`.
use crate::lex::Lexer;
use crate::sexp::{Result, Sexp, parse, read};
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::io::{BufRead, Write};

#[derive(Debug, Default)]
pub struct Stats {
    pub input_steps: usize,
    pub output_steps: usize,
    pub duplicate_steps: usize,
    pub unused_steps: usize,
    pub definitions: usize,
}

/// Hash-consed S-expressions: atoms are `[0, symbol]`, lists `[1, items...]`.
#[derive(Default)]
struct Terms {
    symbols: HashMap<String, u32>,
    names: Vec<String>,
    index: HashMap<Vec<u32>, u32>,
    nodes: Vec<Vec<u32>>,
}

impl Terms {
    fn symbol(&mut self, s: &str) -> u32 {
        if let Some(&id) = self.symbols.get(s) {
            return id;
        }
        self.names.push(s.to_owned());
        self.symbols
            .insert(s.to_owned(), self.names.len() as u32 - 1);
        self.names.len() as u32 - 1
    }

    fn intern(&mut self, key: Vec<u32>) -> u32 {
        if let Some(&id) = self.index.get(&key) {
            return id;
        }
        self.nodes.push(key.clone());
        self.index.insert(key, self.nodes.len() as u32 - 1);
        self.nodes.len() as u32 - 1
    }

    fn add(&mut self, x: &Sexp) -> u32 {
        let key = match x {
            Sexp::Atom(a) => vec![0, self.symbol(a)],
            Sexp::List(xs) => std::iter::once(1)
                .chain(xs.iter().map(|x| self.add(x)))
                .collect(),
        };
        self.intern(key)
    }
}

struct Rule {
    conclusion: Sexp,
    /// Conclusion variables that premises do not determine.
    free: Vec<String>,
}

fn variables(x: &Sexp, out: &mut Vec<String>) {
    match x {
        Sexp::Atom(a) if a.starts_with('?') && !out.contains(a) => out.push(a.clone()),
        Sexp::Atom(_) => {}
        Sexp::List(xs) => xs.iter().for_each(|x| variables(x, out)),
    }
}

fn bind(terms: &Terms, pattern: &Sexp, id: u32, out: &mut HashMap<String, u32>) -> Result<()> {
    let node = &terms.nodes[id as usize];
    match pattern {
        Sexp::Atom(v) if v.starts_with('?') => {
            out.insert(v.clone(), id);
        }
        Sexp::Atom(a) if node[0] == 0 && terms.names[node[1] as usize] == *a => {}
        Sexp::List(ps) if node[0] == 1 && node.len() == ps.len() + 1 => {
            for (p, &a) in ps.iter().zip(&node[1..]) {
                bind(terms, p, a, out)?;
            }
        }
        _ => return Err(format!("conclusion does not match rule pattern {pattern}")),
    }
    Ok(())
}

struct Step {
    rule: String,
    refs: Vec<usize>,
    judgment: u32,
}

struct Writer {
    defs: HashMap<u32, String>,
    uses: HashMap<u32, u32>,
}

impl Writer {
    /// Count how often each compound subterm would be written without sharing.
    fn count(&mut self, terms: &Terms, id: u32) {
        let node = &terms.nodes[id as usize];
        if node[0] == 0 {
            return;
        }
        let n = self.uses.entry(id).or_default();
        *n += 1;
        if *n == 1 {
            node[1..].iter().for_each(|&a| self.count(terms, a));
        }
    }

    fn term(&mut self, terms: &Terms, id: u32, defs: &mut String, out: &mut String) {
        let node = &terms.nodes[id as usize];
        if node[0] == 0 {
            out.push_str(&terms.names[node[1] as usize]);
            return;
        }
        if let Some(name) = self.defs.get(&id) {
            out.push_str(name);
            return;
        }
        let mut text = String::from("(");
        for (i, &a) in node[1..].iter().enumerate() {
            if i > 0 {
                text.push(' ');
            }
            self.term(terms, a, defs, &mut text);
        }
        text.push(')');
        if self.uses.get(&id).copied().unwrap_or(0) < 2 {
            out.push_str(&text);
            return;
        }
        let name = format!("?{}", base36(self.defs.len()));
        let _ = writeln!(defs, "(def {name} {text})");
        out.push_str(&name);
        self.defs.insert(id, name);
    }
}

fn base36(mut n: usize) -> String {
    let mut digits = Vec::new();
    loop {
        digits.push(b"0123456789abcdefghijklmnopqrstuvwxyz"[n % 36]);
        n /= 36;
        if n == 0 {
            break;
        }
    }
    digits.iter().rev().map(|&d| d as char).collect()
}

/// Rewrite an ordinary certificate (`step` forms with stated conclusions and
/// `result` forms) into compact form. The input is not validated.
pub fn compress(theory: &str, proof: impl BufRead, mut out: impl Write) -> Result<Stats> {
    let mut rules = HashMap::new();
    for form in parse(theory)? {
        let xs = form.list()?;
        if xs.len() == 4 && xs[0].atom()? == "rule" {
            let (mut bound, mut free) = (Vec::new(), Vec::new());
            xs[2].list()?.iter().for_each(|p| variables(p, &mut bound));
            variables(&xs[3], &mut free);
            free.retain(|v| !bound.contains(v));
            let conclusion = xs[3].clone();
            rules.insert(xs[1].atom()?.to_owned(), Rule { conclusion, free });
        }
    }
    let mut terms = Terms::default();
    let (mut steps, mut results) = (Vec::new(), Vec::new());
    let lexer = &mut Lexer::new(proof);
    while lexer.peek()?.is_some() {
        let form = read(lexer, 0)?;
        let xs = form.list()?;
        let index =
            |x: &Sexp| -> Result<usize> { x.atom()?.parse().map_err(|_| "bad index".into()) };
        match (xs.first().map(Sexp::atom).transpose()?, xs.len()) {
            (Some("step"), 5) => steps.push(Step {
                rule: xs[2].atom()?.to_owned(),
                refs: xs[3].list()?.iter().map(index).collect::<Result<_>>()?,
                judgment: terms.add(&xs[4]),
            }),
            (Some("result"), 3) => results.push((xs[1].atom()?.to_owned(), index(&xs[2])?)),
            _ => return Err(format!("unsupported proof form: {form}")),
        }
    }
    // Replace each step by the first step with the same judgment.
    let mut first = HashMap::new();
    let canon: Vec<usize> = (0..steps.len())
        .map(|i| *first.entry(steps[i].judgment).or_insert(i))
        .collect();
    let mut live = vec![false; steps.len()];
    for &(_, i) in &results {
        *live.get_mut(i).ok_or("result refers to a missing step")? = true;
    }
    for i in (0..steps.len()).rev() {
        if live[i] {
            live[canon[i]] = true;
            for &r in &steps[canon[i]].refs {
                *live.get_mut(r).ok_or("missing premise")? = true;
            }
        }
    }
    let kept: Vec<usize> = (0..steps.len())
        .filter(|&i| live[i] && canon[i] == i)
        .collect();
    let mut number = vec![usize::MAX; steps.len()];
    for (n, &i) in kept.iter().enumerate() {
        number[i] = n;
    }
    let mut bindings = Vec::with_capacity(kept.len());
    let mut writer = Writer {
        defs: HashMap::new(),
        uses: HashMap::new(),
    };
    for &i in &kept {
        let rule = rules
            .get(&steps[i].rule)
            .ok_or_else(|| format!("unknown rule {}", steps[i].rule))?;
        let mut all = HashMap::new();
        if !rule.free.is_empty() {
            bind(&terms, &rule.conclusion, steps[i].judgment, &mut all)?;
        }
        let values: Vec<(&str, u32)> = rule.free.iter().map(|v| (v.as_str(), all[v])).collect();
        values.iter().for_each(|&(_, t)| writer.count(&terms, t));
        bindings.push(values);
    }
    let io = |e: std::io::Error| e.to_string();
    let (mut defs, mut line) = (String::new(), String::new());
    for (n, (&i, values)) in kept.iter().zip(&bindings).enumerate() {
        line.clear();
        let refs: Vec<String> = steps[i]
            .refs
            .iter()
            .map(|&r| number[canon[r]].to_string())
            .collect();
        let _ = write!(line, "(step {n} {} ({})", steps[i].rule, refs.join(" "));
        for &(v, t) in values {
            let _ = write!(line, " ({v} ");
            writer.term(&terms, t, &mut defs, &mut line);
            line.push(')');
        }
        line.push_str(")\n");
        out.write_all(defs.as_bytes()).map_err(io)?;
        out.write_all(line.as_bytes()).map_err(io)?;
        defs.clear();
    }
    for (name, i) in &results {
        writeln!(out, "(result {name} {})", number[canon[*i]]).map_err(io)?;
    }
    out.flush().map_err(io)?;
    let unique: HashSet<_> = canon.iter().collect();
    Ok(Stats {
        input_steps: steps.len(),
        output_steps: kept.len(),
        duplicate_steps: steps.len() - unique.len(),
        unused_steps: unique.len() - kept.len(),
        definitions: writer.defs.len(),
    })
}
