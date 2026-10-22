//! Untrusted research tool: generalize a ground certificate.
//!
//! The *skeleton* of a step is its rule together with the skeletons of its
//! premises, ignoring every term. Steps with the same skeleton are instances
//! of one derived rule: composing the skeleton's rules by unification gives
//! its most general judgment, and every step of that skeleton concludes a
//! ground instance of it. This is explanation-based generalization applied to
//! Horn certificates.
//!
//! Steps concluding a *cut* predicate are not generalized through. Their
//! arguments become flexible variables that are never fixed to the values
//! the ground proof happened to use. A variable that the rest of the proof
//! links to one of these becomes flexible too. When a goal's statement keeps
//! a flexible variable, the proof may hold for every value of it.
//!
//! `emit` tests that: it instantiates every flexible variable to one
//! eigenvariable, re-derives each cut judgment by backward chaining with the
//! theory's own rules, falling back to structural induction on the
//! eigenvariable, and writes the result as a schematic certificate for
//! `horn::schematic`. Nothing here is trusted; the schematic checker decides.
use crate::oracle::{Map, Pat, Set, Spec, Store, Truth, deep, read_goals, read_truth};
use crate::sexp::Result;
use std::fmt::Write as _;
use std::io::{BufRead, Write};

const NONE: u32 = u32::MAX;
/// Head of a pattern variable node `[VAR, number, sort]`.
const VAR: u32 = u32::MAX - 1;
const PROP: u32 = u32::MAX;

/// Mutable term graph for unification; variables link to their binding.
#[derive(Default, Clone)]
struct Graph {
    head: Vec<u32>,
    start: Vec<u32>,
    kids: Vec<u32>,
    link: Vec<u32>,
    sort: Vec<u32>,
    flex: Vec<bool>,
    /// Rigid variables are eigenvariables: they unify only with themselves.
    rigid: Vec<bool>,
}

impl Graph {
    fn clear(&mut self) {
        self.head.clear();
        self.start.clear();
        self.kids.clear();
        self.link.clear();
        self.sort.clear();
        self.flex.clear();
        self.rigid.clear();
    }

    fn var(&mut self, sort: u32, flex: bool) -> u32 {
        let v = self.push(VAR, sort, &[]);
        self.flex[v as usize] = flex;
        v
    }

    fn push(&mut self, head: u32, sort: u32, args: &[u32]) -> u32 {
        let id = self.head.len() as u32;
        self.head.push(head);
        self.start.push(self.kids.len() as u32);
        self.kids.extend_from_slice(args);
        self.link.push(NONE);
        self.sort.push(sort);
        self.flex.push(false);
        self.rigid.push(false);
        id
    }

    fn args(&self, x: u32, arity: usize) -> &[u32] {
        let s = self.start[x as usize] as usize;
        &self.kids[s..s + arity]
    }

    /// The representative of a node. Unified compound nodes are linked too,
    /// so a pair is never unified twice.
    fn find(&self, mut x: u32) -> u32 {
        while self.link[x as usize] != NONE {
            x = self.link[x as usize];
        }
        x
    }

    fn root(&mut self, x: u32) -> u32 {
        let r = self.find(x);
        let mut x = x;
        while self.link[x as usize] != NONE {
            let next = self.link[x as usize];
            self.link[x as usize] = r;
            x = next;
        }
        r
    }

    /// Link variable `a` to `b`; a flexible variable makes its class flexible.
    fn bind(&mut self, a: u32, b: u32) {
        self.link[a as usize] = b;
        if self.head[b as usize] == VAR {
            self.flex[b as usize] |= self.flex[a as usize];
        }
    }

    fn unify(&mut self, spec: &Spec, a: u32, b: u32) -> Result<()> {
        let mut work = vec![(a, b)];
        while let Some((a, b)) = work.pop() {
            let (a, b) = (self.root(a), self.root(b));
            if a == b {
                continue;
            }
            let free = |x: u32| self.head[x as usize] == VAR && !self.rigid[x as usize];
            match (self.head[a as usize], self.head[b as usize]) {
                _ if free(a) => self.bind(a, b),
                _ if free(b) => self.bind(b, a),
                (VAR, _) | (_, VAR) => return Err("an eigenvariable does not unify".into()),
                (h, k) if h == k => {
                    let n = spec.inputs[h as usize].len();
                    for i in 0..n {
                        work.push((self.args(a, n)[i], self.args(b, n)[i]));
                    }
                    self.link[a as usize] = b;
                }
                _ => return Err("skeleton does not unify".into()),
            }
        }
        Ok(())
    }
}

/// A map keyed by dense node numbers that clears in constant time.
struct Memo {
    stamp: Vec<u32>,
    value: Vec<u32>,
    now: u32,
}

impl Memo {
    fn new() -> Self {
        Memo {
            stamp: Vec::new(),
            value: Vec::new(),
            now: 1,
        }
    }

    fn clear(&mut self) {
        self.now += 1;
        if self.now == u32::MAX {
            self.stamp.fill(0);
            self.now = 1;
        }
    }

    fn get(&self, k: u32) -> Option<u32> {
        let k = k as usize;
        (self.stamp.get(k) == Some(&self.now)).then(|| self.value[k])
    }

    fn insert(&mut self, k: u32, v: u32) {
        let k = k as usize;
        if k >= self.stamp.len() {
            self.stamp.resize(k + 1, 0);
            self.value.resize(k + 1, 0);
        }
        self.stamp[k] = self.now;
        self.value[k] = v;
    }
}

/// Empty a per-step table for the next step. Clearing costs its capacity, so
/// a table that one large step grew is dropped instead.
fn reuse<T: Default + Len>(table: &mut T) {
    if table.capacity() > 1 << 12 {
        *table = T::default();
    } else {
        table.clear();
    }
}

trait Len {
    fn capacity(&self) -> usize;
    fn clear(&mut self);
}

impl<K, V> Len for Map<K, V> {
    fn capacity(&self) -> usize {
        Map::capacity(self)
    }
    fn clear(&mut self) {
        Map::clear(self)
    }
}

impl<K> Len for Set<K> {
    fn capacity(&self) -> usize {
        Set::capacity(self)
    }
    fn clear(&mut self) {
        Set::clear(self)
    }
}

/// One derived rule: a skeleton's most general judgment.
struct Class {
    /// Pattern node of the conclusion. Variables are numbered from zero,
    /// first those of the conclusion in first-occurrence order, then
    /// flexible variables that only premises use.
    conclusion: u32,
    flex: Vec<bool>,
}

#[derive(Debug, Default)]
pub struct Stats {
    /// Steps that some result depends on, after merging repeated judgments.
    pub steps: usize,
    /// Distinct skeletons among those steps.
    pub classes: usize,
    /// Distinct ground term and judgment nodes in the input.
    pub ground_nodes: usize,
    /// Distinct pattern nodes over all most general judgments and
    /// substitutions.
    pub pattern_nodes: usize,
    /// Variables of all derived rules, and how many are flexible.
    pub class_vars: usize,
    pub flex_vars: usize,
    /// Variables absent from a conclusion, fixed to the first instance's
    /// ground values.
    pub fixed_vars: usize,
    /// Substitution entries at premise references, and how many are a bare
    /// variable (a renaming).
    pub subst_entries: usize,
    pub subst_renamings: usize,
    /// Classes by number of instances: 1, 2-9, 10-99, 100+.
    pub instance_histogram: [usize; 4],
    pub goals: Vec<Goal>,
}

#[derive(Debug)]
pub struct Goal {
    pub name: String,
    /// The generalized statement, truncated.
    pub general: String,
    /// Each variable of the generalized statement: name and sort, whether it
    /// is flexible, and the goal's value.
    pub vars: Vec<(String, bool, String)>,
}

#[derive(Debug, Default)]
pub struct Emitted {
    /// Goals stated over the eigenvariable.
    pub open_goals: usize,
    /// Goals whose proof pins the variable; they stay ground.
    pub rigid_goals: Vec<String>,
    pub steps: usize,
    pub inductions: usize,
    pub definitions: usize,
}

struct Analysis<'s> {
    spec: &'s Spec,
    /// Output sort of every constructor; `PROP` for predicates.
    output: Vec<u32>,
    ground: Store,
    pat: Store,
    graph: Graph,
    /// Ground node to pattern node.
    lifted: Map<u32, u32>,
    /// Children of the nodes being built by `copy` and `resolve`, as a stack.
    scratch: Vec<u32>,
}

impl Analysis<'_> {
    /// Variables occurring as argument `pos` of constructor `ctor`.
    fn at(&self, p: u32, ctor: u32, pos: usize, out: &mut Set<u32>) {
        let node = self.pat.node(p);
        if node[0] == VAR {
            return;
        }
        if node[0] == ctor {
            let a = self.pat.node(node[pos + 1]);
            if a[0] == VAR {
                out.insert(a[1]);
            }
        }
        for &a in &node[1..] {
            self.at(a, ctor, pos, out);
        }
    }

    fn lift(&mut self, g: u32) -> u32 {
        if let Some(&p) = self.lifted.get(&g) {
            return p;
        }
        let node = self.ground.node(g).to_vec();
        let mut key = vec![node[0]];
        for &a in &node[1..] {
            key.push(self.lift(a));
        }
        let p = self.pat.intern(&key);
        self.lifted.insert(g, p);
        p
    }

    /// Copy a pattern into the graph with fresh variables.
    fn copy(&mut self, p: u32, memo: &mut Memo, class: &Class, vars: &mut [u32]) -> u32 {
        if let Some(x) = memo.get(p) {
            return x;
        }
        let node = self.pat.node(p);
        let (head, arity) = (node[0], node.len() - 1);
        let x = if head == VAR {
            let (number, sort) = (node[1], node[2]);
            let v = self.graph.var(sort, class.flex[number as usize]);
            vars[number as usize] = v;
            v
        } else {
            let base = self.scratch.len();
            for i in 0..arity {
                let a = self.pat.node(p)[i + 1];
                let x = self.copy(a, memo, class, vars);
                self.scratch.push(x);
            }
            let x = self.graph.push(head, NONE, &self.scratch[base..]);
            self.scratch.truncate(base);
            x
        };
        memo.insert(p, x);
        x
    }

    fn instantiate(&mut self, p: &Pat, env: &[u32]) -> u32 {
        match p {
            Pat::Var(v) => env[*v],
            Pat::App(h, args) => {
                let args: Vec<u32> = args.iter().map(|a| self.instantiate(a, env)).collect();
                self.graph.push(*h, NONE, &args)
            }
        }
    }

    /// Read a graph term back as a pattern. Unnumbered variables are fixed
    /// to their ground value if one is recorded, and otherwise numbered when
    /// `number_all` is set or they are flexible.
    fn resolve(
        &mut self,
        x: u32,
        memo: &mut Memo,
        numbering: &mut Map<u32, u32>,
        fixed: &Map<u32, u32>,
        number_all: bool,
    ) -> Result<u32> {
        let x = self.graph.find(x);
        if let Some(p) = memo.get(x) {
            return Ok(p);
        }
        let h = self.graph.head[x as usize];
        let p = if h == VAR {
            if let Some(&g) = fixed.get(&x) {
                self.lift(g)
            } else {
                let k = match numbering.get(&x) {
                    Some(&k) => k,
                    None if number_all || self.graph.flex[x as usize] => {
                        let k = numbering.len() as u32;
                        numbering.insert(x, k);
                        k
                    }
                    None => return Err("unresolved internal variable".into()),
                };
                self.pat.intern(&[VAR, k, self.graph.sort[x as usize]])
            }
        } else {
            let n = self.spec.inputs[h as usize].len();
            let base = self.scratch.len();
            self.scratch.push(h);
            for i in 0..n {
                let a = self.graph.args(x, n)[i];
                match self.resolve(a, memo, numbering, fixed, number_all) {
                    Ok(p) => self.scratch.push(p),
                    Err(e) => {
                        self.scratch.truncate(base);
                        return Err(e);
                    }
                }
            }
            let p = self.pat.intern(&self.scratch[base..]);
            self.scratch.truncate(base);
            p
        };
        memo.insert(x, p);
        Ok(p)
    }

    /// Record ground values for unnumbered rigid variables by walking a graph
    /// term alongside one of its ground instances.
    fn fix(
        &self,
        x: u32,
        g: u32,
        numbering: &Map<u32, u32>,
        fixed: &mut Map<u32, u32>,
        seen: &mut Set<(u32, u32)>,
    ) {
        let x = self.graph.find(x);
        if !seen.insert((x, g)) {
            return;
        }
        let h = self.graph.head[x as usize];
        if h == VAR {
            if !numbering.contains_key(&x) && !self.graph.flex[x as usize] {
                fixed.entry(x).or_insert(g);
            }
            return;
        }
        let n = self.spec.inputs[h as usize].len();
        for i in 0..n {
            let a = self.graph.args(x, n)[i];
            let b = self.ground.node(g)[i + 1];
            self.fix(a, b, numbering, fixed, seen);
        }
    }

    fn show(&self, p: u32, budget: &mut usize, var: &dyn Fn(u32) -> String) -> String {
        if *budget == 0 {
            return "…".into();
        }
        *budget -= 1;
        let node = self.pat.node(p);
        if node[0] == VAR {
            return var(node[1]);
        }
        let name = &self.spec.names[node[0] as usize];
        if node.len() == 1 && self.output[node[0] as usize] != PROP {
            return name.clone();
        }
        let mut s = format!("({name}");
        for &a in &node[1..] {
            s.push(' ');
            s.push_str(&self.show(a, budget, var));
        }
        s.push(')');
        s
    }

    fn show_ground(&self, g: u32, budget: &mut usize) -> String {
        if *budget == 0 {
            return "…".into();
        }
        *budget -= 1;
        let node = self.ground.node(g);
        let name = &self.spec.names[node[0] as usize];
        if node.len() == 1 {
            return name.clone();
        }
        let mut s = format!("({name}");
        for &a in &node[1..] {
            s.push(' ');
            s.push_str(&self.show_ground(a, budget));
        }
        s.push(')');
        s
    }

    /// Match a ground term against a pattern, recording variable values.
    fn bind(&self, p: u32, g: u32, out: &mut Map<u32, u32>) {
        let node = self.pat.node(p);
        if node[0] == VAR {
            out.entry(node[1]).or_insert(g);
            return;
        }
        for (i, &a) in node[1..].iter().enumerate() {
            self.bind(a, self.ground.node(g)[i + 1], out);
        }
    }
}

/// `PRED` or `PRED:POSITION,...`: the positions are functional outputs.
fn parse_cut(spec: &Spec, cut: &[&str]) -> Result<Map<u32, Vec<usize>>> {
    cut.iter()
        .map(|c| {
            let mut parts = c.split(':');
            let p = parts.next().unwrap_or_default();
            let id = spec.preds.get(p).copied();
            let id = id.ok_or_else(|| format!("unknown predicate {p}"))?;
            let outputs = parts
                .map(|o| o.parse().map_err(|_| format!("bad position {o}")))
                .collect::<Result<Vec<usize>>>()?;
            Ok((id, outputs))
        })
        .collect()
}

/// Analyze a certificate, and with `out` also write a schematic goals file
/// and certificate (see the module documentation).
pub fn generalize(
    theory: &str,
    goals: &str,
    proof: impl BufRead + Send,
    cut: &[&str],
    abstract_at: Option<&str>,
    out: Option<(&mut (dyn Write + Send), &mut (dyn Write + Send))>,
) -> Result<(Stats, Option<Emitted>)> {
    let spec = Spec::parse(theory)?;
    let cut = parse_cut(&spec, cut)?;
    let abstract_at = match abstract_at {
        Some(a) => {
            let (c, p) = a.split_once(':').ok_or("expected CONSTRUCTOR:POSITION")?;
            let c = spec
                .ctors
                .get(c)
                .copied()
                .ok_or_else(|| format!("unknown constructor {c}"))?;
            Some((c, p.parse().map_err(|_| format!("bad position {p}"))?))
        }
        None => None,
    };
    deep(|| run(&spec, goals, proof, &cut, abstract_at, out))
}

fn run(
    spec: &Spec,
    goals_source: &str,
    proof: impl BufRead,
    cut: &Map<u32, Vec<usize>>,
    abstract_at: Option<(u32, usize)>,
    out: Option<(&mut (dyn Write + Send), &mut (dyn Write + Send))>,
) -> Result<(Stats, Option<Emitted>)> {
    let mut ground = Store::new();
    let goals = read_goals(spec, &mut ground, goals_source)?;
    let truth = read_truth(spec, &mut ground, proof)?;
    let n = truth.rule.len();

    // Merge repeated judgments into their first step, then keep only steps
    // that some result depends on.
    let mut first: Map<u32, u32> = Map::default();
    let canon: Vec<u32> = (0..n as u32)
        .map(|s| *first.entry(truth.judgment[s as usize]).or_insert(s))
        .collect();
    let is_cut = |g: &Store, s: usize| cut.contains_key(&g.node(truth.judgment[s])[0]);
    let mut needed = vec![false; n];
    let mut stack: Vec<u32> = truth.results.values().map(|&s| canon[s as usize]).collect();
    while let Some(s) = stack.pop() {
        if !std::mem::replace(&mut needed[s as usize], true) && !is_cut(&ground, s as usize) {
            stack.extend(truth.refs[s as usize].iter().map(|&r| canon[r as usize]));
        }
    }

    let mut output = vec![PROP; spec.names.len()];
    for (sort, ctors) in spec.by_sort.iter().enumerate() {
        for &c in ctors {
            output[c as usize] = sort as u32;
        }
    }
    let mut an = Analysis {
        spec,
        output,
        ground,
        pat: Store::new(),
        graph: Graph::default(),
        lifted: Map::default(),
        scratch: Vec::new(),
    };
    let mut stats = Stats {
        ground_nodes: an.ground.len(),
        ..Stats::default()
    };
    let mut skeletons: Map<Vec<u32>, u32> = Map::default();
    let mut classes: Vec<Class> = Vec::new();
    let mut instances: Vec<usize> = Vec::new();
    let mut class_of = vec![NONE; n];
    let mut copy_memo = Memo::new();
    let mut memo = Memo::new();
    // Per-step tables, emptied at the end of each step rather than rebuilt.
    let (mut numbering, mut fixed, mut seen) = (Map::default(), Map::default(), Set::default());
    let none = Map::default();
    for s in 0..n {
        if !needed[s] {
            continue;
        }
        stats.steps += 1;
        if is_cut(&an.ground, s) {
            let pred = an.ground.node(truth.judgment[s])[0];
            let key = vec![VAR, pred];
            let c = match skeletons.get(&key) {
                Some(&c) => c,
                None => {
                    let inputs = &spec.inputs[pred as usize];
                    let mut node = vec![pred];
                    for (k, &so) in inputs.iter().enumerate() {
                        node.push(an.pat.intern(&[VAR, k as u32, so]));
                    }
                    let c = classes.len() as u32;
                    classes.push(Class {
                        conclusion: an.pat.intern(&node),
                        flex: vec![true; inputs.len()],
                    });
                    instances.push(0);
                    skeletons.insert(key, c);
                    c
                }
            };
            instances[c as usize] += 1;
            class_of[s] = c;
            continue;
        }
        let refs: Vec<u32> = truth.refs[s].iter().map(|&r| canon[r as usize]).collect();
        let mut key = vec![truth.rule[s]];
        key.extend(refs.iter().map(|&r| class_of[r as usize]));
        if let Some(&c) = skeletons.get(&key) {
            class_of[s] = c;
            instances[c as usize] += 1;
            continue;
        }
        let rule = &spec.rules[truth.rule[s] as usize];
        an.graph.clear();
        let env: Vec<u32> = rule
            .vars
            .iter()
            .map(|&(_, so)| an.graph.var(so, false))
            .collect();
        let mut premises = Vec::new();
        let mut copies = Vec::new();
        for (p, &r) in rule.premises.iter().zip(&refs) {
            let child = class_of[r as usize];
            let child = &classes[child as usize];
            let mut vars = vec![NONE; child.flex.len()];
            copy_memo.clear();
            let copy = an.copy(child.conclusion, &mut copy_memo, child, &mut vars);
            let inst = an.instantiate(p, &env);
            an.graph.unify(spec, inst, copy)?;
            premises.push((inst, truth.judgment[r as usize]));
            copies.push(vars);
        }
        let conclusion = an.instantiate(&rule.conclusion, &env);
        memo.clear();
        let pattern = an.resolve(conclusion, &mut memo, &mut numbering, &none, true)?;
        // Rigid variables absent from the conclusion take the first
        // instance's ground values; that instance proves the result.
        for &(inst, g) in &premises {
            an.fix(inst, g, &numbering, &mut fixed, &mut seen);
        }
        stats.fixed_vars += fixed.len();
        // Number the flexible variables that only premises use, and count
        // what each premise reference would have to substitute.
        for &v in copies.iter().flatten().filter(|&&v| v != NONE) {
            let p = an.resolve(v, &mut memo, &mut numbering, &fixed, false)?;
            stats.subst_entries += 1;
            stats.subst_renamings += usize::from(an.pat.node(p)[0] == VAR);
        }
        let mut flex = vec![false; numbering.len()];
        for (&x, &k) in &numbering {
            flex[k as usize] = an.graph.flex[x as usize];
        }
        // Empty the step's tables now, so that a table one large step grew
        // is released before the next step builds anything.
        reuse(&mut numbering);
        reuse(&mut fixed);
        reuse(&mut seen);
        stats.class_vars += flex.len();
        stats.flex_vars += flex.iter().filter(|&&f| f).count();
        let c = classes.len() as u32;
        classes.push(Class {
            conclusion: pattern,
            flex,
        });
        instances.push(1);
        skeletons.insert(key, c);
        class_of[s] = c;
    }
    stats.classes = classes.len();
    for &k in &instances {
        stats.instance_histogram[match k {
            0 | 1 => 0,
            2..=9 => 1,
            10..=99 => 2,
            _ => 3,
        }] += 1;
    }
    let mut roots = Vec::new();
    for (name, g) in goals {
        let s = *truth
            .results
            .get(&name)
            .ok_or_else(|| format!("no result for goal {name}"))?;
        let c = class_of[canon[s as usize] as usize];
        let class = &classes[c as usize];
        let mut values = Map::default();
        an.bind(class.conclusion, g, &mut values);
        let mut vars: Vec<(u32, String, bool, String)> = values
            .iter()
            .map(|(&k, &v)| {
                let sort = an.output[an.ground.node(v)[0] as usize];
                let sort = spec
                    .sorts
                    .iter()
                    .find(|&(_, &i)| i == sort)
                    .map_or("?".to_owned(), |(n, _)| n.clone());
                let shown = an.show_ground(v, &mut 12);
                (k, sort, class.flex[k as usize], shown)
            })
            .collect();
        vars.sort();
        let budget = &mut std::env::var("HORN_SHOW")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(60);
        stats.goals.push(Goal {
            general: an.show(class.conclusion, budget, &|k| format!("?v{k}")),
            name: name.clone(),
            vars: vars
                .into_iter()
                .map(|(k, s, f, v)| (format!("?v{k} : {s}"), f, v))
                .collect(),
        });
        roots.push((name, c, values, canon[s as usize]));
    }
    stats.pattern_nodes = an.pat.len();
    let emitted = match out {
        Some((goals_out, proof_out)) => {
            let input = Input {
                truth: &truth,
                canon: &canon,
                cut,
                open: roots
                    .iter()
                    .map(|(_, c, _, _)| {
                        let class = &classes[*c as usize];
                        let mut open = Set::default();
                        match abstract_at {
                            Some((ctor, pos)) => an.at(class.conclusion, ctor, pos, &mut open),
                            None => open.extend(
                                (0..class.flex.len() as u32).filter(|&k| class.flex[k as usize]),
                            ),
                        }
                        open
                    })
                    .collect(),
            };
            Some(emit(
                &mut an, &classes, &roots, &input, goals_out, proof_out,
            )?)
        }
        None => None,
    };
    Ok((stats, emitted))
}

struct Input<'a> {
    truth: &'a Truth,
    canon: &'a [u32],
    cut: &'a Map<u32, Vec<usize>>,
    /// For each goal, the variables of its generalized statement to replace
    /// by the eigenvariable.
    open: Vec<Set<u32>>,
}

struct Emitter<'a, 's> {
    an: &'a mut Analysis<'s>,
    out: String,
    stats: Emitted,
    /// Pattern node of the eigenvariable, and its name.
    eigen: u32,
    eigen_name: String,
    proved: Map<u32, u32>,
    /// Steps already written, by judgment.
    derived: Map<u32, u32>,
    /// Hypotheses in scope during an induction case, by judgment.
    hyps: Map<u32, u32>,
    defs: Map<u32, String>,
    /// Names of case variables, by pattern node.
    names: Map<u32, String>,
}
struct Snapshot {
    out: usize,
    steps: usize,
    inductions: usize,
    definitions: usize,
    proved: Map<u32, u32>,
    derived: Map<u32, u32>,
    defs: Map<u32, String>,
    names: Map<u32, String>,
}

impl Emitter<'_, '_> {
    fn snapshot(&self) -> Snapshot {
        Snapshot {
            out: self.out.len(),
            steps: self.stats.steps,
            inductions: self.stats.inductions,
            definitions: self.stats.definitions,
            proved: self.proved.clone(),
            derived: self.derived.clone(),
            defs: self.defs.clone(),
            names: self.names.clone(),
        }
    }

    fn restore(&mut self, s: Snapshot) {
        self.out.truncate(s.out);
        self.stats.steps = s.steps;
        self.stats.inductions = s.inductions;
        self.stats.definitions = s.definitions;
        self.proved = s.proved;
        self.derived = s.derived;
        self.defs = s.defs;
        self.names = s.names;
        self.hyps.clear();
    }

    fn term(&mut self, p: u32) -> String {
        if let Some(name) = self.names.get(&p) {
            return name.clone();
        }
        let node = self.an.pat.node(p).to_vec();
        if node[0] == VAR {
            return self.eigen_name.clone();
        }
        if node.len() == 1 {
            return self.an.spec.names[node[0] as usize].clone();
        }
        if let Some(d) = self.defs.get(&p) {
            return d.clone();
        }
        let args: Vec<String> = node[1..].iter().map(|&a| self.term(a)).collect();
        let name = format!("?d{}", self.defs.len());
        let _ = writeln!(
            self.out,
            "(def {name} ({} {}))",
            self.an.spec.names[node[0] as usize],
            args.join(" ")
        );
        self.defs.insert(p, name.clone());
        self.stats.definitions += 1;
        name
    }

    fn judgment(&mut self, j: u32) -> String {
        let node = self.an.pat.node(j).to_vec();
        let args: Vec<String> = node[1..].iter().map(|&a| self.term(a)).collect();
        let pred = &self.an.spec.names[node[0] as usize];
        if args.is_empty() {
            format!("({pred})")
        } else {
            format!("({pred} {})", args.join(" "))
        }
    }

    fn step(&mut self, rule: &str, refs: &[u32], j: u32) -> u32 {
        let judgment = self.judgment(j);
        let n = self.stats.steps as u32;
        let refs: Vec<String> = refs.iter().map(u32::to_string).collect();
        let _ = writeln!(
            self.out,
            "(step {n} {rule} ({}) {judgment})",
            refs.join(" ")
        );
        self.stats.steps += 1;
        n
    }

    fn mentions(&self, p: u32, x: u32) -> bool {
        let node = self.an.pat.node(p);
        p == x || node[0] != VAR && node[1..].iter().any(|&a| self.mentions(a, x))
    }

    /// Derive a cut judgment by backward chaining with the theory's rules;
    /// if none applies and it mentions the eigenvariable, by induction on it.
    fn prove(&mut self, j: u32, depth: usize) -> Result<u32> {
        if let Some(&n) = self.proved.get(&j).or_else(|| self.hyps.get(&j)) {
            return Ok(n);
        }
        if depth > 4096 {
            return Err("cut judgment too deep".into());
        }
        if let Some(n) = self.chain(j, depth)? {
            if self.hyps.is_empty() {
                self.proved.insert(j, n);
            }
            return Ok(n);
        }
        if depth > 0 || !self.mentions(j, self.eigen) {
            return Err(format!("cannot derive {}", self.show(j)));
        }
        let n = self.induct(j)?;
        self.proved.insert(j, n);
        Ok(n)
    }

    fn chain(&mut self, j: u32, depth: usize) -> Result<Option<u32>> {
        let spec = self.an.spec;
        let pred = self.an.pat.node(j)[0];
        for &r in &spec.by_pred[pred as usize] {
            let rule = &spec.rules[r as usize];
            let mut env = vec![NONE; rule.vars.len()];
            if !match_pat(&self.an.pat, &rule.conclusion, j, &mut env) {
                continue;
            }
            let mut premises = Vec::new();
            for p in &rule.premises {
                match build_pat(&mut self.an.pat, p, &env) {
                    Some(q) => premises.push(q),
                    None => break,
                }
            }
            if premises.len() != rule.premises.len() {
                continue;
            }
            let mut refs = Vec::new();
            for &q in &premises {
                match self.prove(q, depth + 1) {
                    Ok(n) => refs.push(n),
                    Err(_) => break,
                }
            }
            if refs.len() == premises.len() {
                let name = rule.name.clone();
                return Ok(Some(self.step(&name, &refs, j)));
            }
        }
        Ok(None)
    }

    /// Structural induction on the eigenvariable. Case variables are fresh
    /// atoms, so judgments about them never meet judgments outside the case.
    fn induct(&mut self, j: u32) -> Result<u32> {
        let sort = self.an.pat.node(self.eigen)[2];
        let ctors = self.an.spec.by_sort[sort as usize].clone();
        let mut cases = Vec::new();
        for c in ctors {
            let inputs = self.an.spec.inputs[c as usize].clone();
            let mut key = vec![c];
            let mut names = Vec::new();
            let mut ihs = Vec::new();
            for &s in &inputs {
                let k = self.names.len() as u32;
                let v = self.an.pat.intern(&[VAR, u32::MAX / 2 + k, s]);
                let name = format!("{}{k}", self.eigen_name);
                let _ = writeln!(self.out, "(var {name} {})", sort_name(self.an.spec, s));
                self.names.insert(v, name.clone());
                names.push(name);
                key.push(v);
                if s == sort {
                    ihs.push(v);
                }
            }
            let term = self.an.pat.intern(&key);
            for &v in &ihs {
                let h = replace(&mut self.an.pat, j, self.eigen, v);
                let hj = self.judgment(h);
                let n = self.stats.steps as u32;
                let _ = writeln!(self.out, "(hyp {n} {hj})");
                self.stats.steps += 1;
                self.hyps.insert(h, n);
            }
            let goal = replace(&mut self.an.pat, j, self.eigen, term);
            let m = self.chain(goal, 1)?;
            self.hyps.clear();
            let m = m.ok_or_else(|| format!("induction case fails: {}", self.show(goal)))?;
            cases.push(if names.is_empty() {
                format!("({m})")
            } else {
                format!("({m} {})", names.join(" "))
            });
        }
        let hj = self.judgment(j);
        let n = self.stats.steps as u32;
        let _ = writeln!(
            self.out,
            "(induct {n} {} {hj} ({}))",
            self.eigen_name,
            cases.join(" ")
        );
        self.stats.steps += 1;
        self.stats.inductions += 1;
        Ok(n)
    }

    fn show(&self, p: u32) -> String {
        let name = self.eigen_name.clone();
        self.an.show(p, &mut 40, &|_| name.clone())
    }
}

fn sort_name(spec: &Spec, s: u32) -> String {
    spec.sorts
        .iter()
        .find(|&(_, &i)| i == s)
        .map(|(n, _)| n.clone())
        .unwrap_or_default()
}

fn match_pat(store: &Store, p: &Pat, id: u32, env: &mut [u32]) -> bool {
    match p {
        Pat::Var(v) if env[*v] == NONE => {
            env[*v] = id;
            true
        }
        Pat::Var(v) => env[*v] == id,
        Pat::App(head, args) => {
            let node = store.node(id);
            node[0] == *head
                && node.len() == args.len() + 1
                && args
                    .iter()
                    .enumerate()
                    .all(|(i, a)| match_pat(store, a, store.node(id)[i + 1], env))
        }
    }
}

fn build_pat(store: &mut Store, p: &Pat, env: &[u32]) -> Option<u32> {
    match p {
        Pat::Var(v) => (env[*v] != NONE).then_some(env[*v]),
        Pat::App(head, args) => {
            let mut key = vec![*head];
            for a in args {
                key.push(build_pat(store, a, env)?);
            }
            Some(store.intern(&key))
        }
    }
}

fn replace(store: &mut Store, p: u32, from: u32, to: u32) -> u32 {
    if p == from {
        return to;
    }
    let node = store.node(p).to_vec();
    if node.len() == 1 || node[0] == VAR {
        return p;
    }
    let mut key = vec![node[0]];
    for &a in &node[1..] {
        key.push(replace(store, a, from, to));
    }
    store.intern(&key)
}

/// The whole needed derivation as one unification problem over the graph.
#[derive(Clone)]
struct Global {
    g: Graph,
    judgment: Vec<u32>,
    lowered: Map<u32, u32>,
    eigen: u32,
}

impl Global {
    /// A ground node as a graph term.
    fn lower(&mut self, an: &Analysis, g: u32) -> u32 {
        if let Some(&x) = self.lowered.get(&g) {
            return x;
        }
        let node = an.ground.node(g).to_vec();
        let args: Vec<u32> = node[1..].iter().map(|&a| self.lower(an, a)).collect();
        let x = self.g.push(node[0], NONE, &args);
        self.lowered.insert(g, x);
        x
    }

    /// A pattern as a graph term; the eigenvariable is the rigid variable.
    fn lower_pattern(
        &mut self,
        an: &Analysis,
        p: u32,
        var: &mut dyn FnMut(&mut Self, u32) -> u32,
    ) -> u32 {
        let node = an.pat.node(p).to_vec();
        if node[0] == VAR {
            return var(self, node[1]);
        }
        let args: Vec<u32> = node[1..]
            .iter()
            .map(|&a| self.lower_pattern(an, a, var))
            .collect();
        self.g.push(node[0], NONE, &args)
    }

    /// Read a graph term back as a pattern, or `None` while a variable in it
    /// is unbound.
    fn raise(
        &self,
        an: &mut Analysis,
        x: u32,
        eigen: u32,
        memo: &mut Map<u32, u32>,
        depth: usize,
    ) -> Option<u32> {
        let x = self.g.find(x);
        if let Some(&p) = memo.get(&x) {
            return Some(p);
        }
        if depth > 1 << 16 {
            return None;
        }
        let h = self.g.head[x as usize];
        let p = if h == VAR {
            (x == self.eigen).then_some(eigen)?
        } else {
            let n = an.spec.inputs[h as usize].len();
            let mut key = vec![h];
            for i in 0..n {
                key.push(self.raise(an, self.g.args(x, n)[i], eigen, memo, depth + 1)?);
            }
            an.pat.intern(&key)
        };
        memo.insert(x, p);
        Some(p)
    }

    /// Bind unbound variables to the values of a ground instance.
    fn settle(&mut self, an: &Analysis, x: u32, g: u32, seen: &mut Set<(u32, u32)>) {
        let x = self.g.find(x);
        if !seen.insert((x, g)) {
            return;
        }
        let h = self.g.head[x as usize];
        if h == VAR {
            if x != self.eigen {
                let y = self.lower(an, g);
                self.g.bind(x, y);
            }
            return;
        }
        let n = an.spec.inputs[h as usize].len();
        for i in 0..n {
            let a = self.g.args(x, n)[i];
            let b = an.ground.node(g)[i + 1];
            self.settle(an, a, b, seen);
        }
    }
}

fn instantiate(g: &mut Graph, p: &Pat, env: &[u32]) -> u32 {
    match p {
        Pat::Var(v) => env[*v],
        Pat::App(h, args) => {
            let args: Vec<u32> = args.iter().map(|a| instantiate(g, a, env)).collect();
            g.push(*h, NONE, &args)
        }
    }
}

/// Re-derive each goal with the chosen variables of its statement replaced
/// by one rigid eigenvariable. Each goal gets its own unification problem
/// over the steps it needs, so steps shared with other goals do not pin it.
/// Cut judgments are re-derived; a functional output left open takes the
/// first candidate that can be derived: one of the judgment's other
/// arguments of the same sort, or the ground proof's value. Everything still
/// open takes the ground proof's value. A goal that fails is written with its
/// ground statement instead.
fn emit(
    an: &mut Analysis,
    classes: &[Class],
    roots: &[(String, u32, Map<u32, u32>, u32)],
    input: &Input,
    goals_out: &mut (dyn Write + Send),
    proof_out: &mut (dyn Write + Send),
) -> Result<Emitted> {
    let spec = an.spec;
    let mut sorts = Set::default();
    for (i, (_, _, values, _)) in roots.iter().enumerate() {
        for &k in values.keys() {
            if input.open[i].contains(&k) {
                sorts.insert(an.output[an.ground.node(values[&k])[0] as usize]);
            }
        }
    }
    if sorts.len() > 1 {
        return Err("abstracted goal variables of more than one sort".into());
    }
    let sort = sorts.into_iter().next().unwrap_or(0);
    let mut eigen_name = "L".to_owned();
    while spec.ctors.contains_key(&eigen_name) || spec.preds.contains_key(&eigen_name) {
        eigen_name.push('_');
    }
    let eigen = an.pat.intern(&[VAR, u32::MAX / 4, sort]);
    let mut em = Emitter {
        an,
        out: String::new(),
        stats: Emitted::default(),
        eigen,
        eigen_name: eigen_name.clone(),
        proved: Map::default(),
        derived: Map::default(),
        hyps: Map::default(),
        defs: Map::default(),
        names: Map::default(),
    };
    let mut goals_text = format!("(var {eigen_name} {})\n", sort_name(spec, sort));
    let mut results = String::new();
    for (i, root) in roots.iter().enumerate() {
        let saved = em.snapshot();
        let (n, j) = match derive_goal(&mut em, classes, root, input, Some(&input.open[i]), sort) {
            Ok(r) => {
                em.stats.open_goals += 1;
                r
            }
            Err(e) => {
                if std::env::var_os("HORN_DEBUG").is_some() {
                    eprintln!("goal {} stays ground: {e}", root.0);
                }
                em.restore(saved);
                em.stats.rigid_goals.push(root.0.clone());
                derive_goal(&mut em, classes, root, input, None, sort)?
            }
        };
        let shown = em.an.show(j, &mut { usize::MAX }, &|_| eigen_name.clone());
        let _ = writeln!(goals_text, "(goal {} {shown})", root.0);
        let _ = writeln!(results, "(result {} {n})", root.0);
    }
    em.out.push_str(&results);
    proof_out
        .write_all(em.out.as_bytes())
        .map_err(|e| e.to_string())?;
    goals_out
        .write_all(goals_text.as_bytes())
        .map_err(|e| e.to_string())?;
    Ok(em.stats)
}

/// Write the derivation of one goal; with `open`, those variables of its
/// generalized statement become the eigenvariable. Returns the step index
/// and the statement.
fn derive_goal(
    em: &mut Emitter,
    classes: &[Class],
    (name, c, values, root): &(String, u32, Map<u32, u32>, u32),
    input: &Input,
    open: Option<&Set<u32>>,
    sort: u32,
) -> Result<(u32, u32)> {
    let spec = em.an.spec;
    let truth = input.truth;
    let is_cut = |an: &Analysis, s: usize| {
        input
            .cut
            .contains_key(&an.ground.node(truth.judgment[s])[0])
    };
    // The steps this goal needs, stopping at cut judgments.
    let mut mine = vec![false; truth.rule.len()];
    let mut stack = vec![*root];
    while let Some(s) = stack.pop() {
        if !std::mem::replace(&mut mine[s as usize], true) && !is_cut(em.an, s as usize) {
            stack.extend(
                truth.refs[s as usize]
                    .iter()
                    .map(|&r| input.canon[r as usize]),
            );
        }
    }
    let mut gl = Global {
        g: Graph::default(),
        judgment: vec![NONE; truth.rule.len()],
        lowered: Map::default(),
        eigen: NONE,
    };
    gl.eigen = gl.g.var(sort, false);
    gl.g.rigid[gl.eigen as usize] = true;
    // Each use of a cut judgment gets its own variables: one ground fact,
    // such as `max z z z`, may stand for differently generalized ones.
    let mut cuts = Vec::new();
    let mut uses: Vec<Vec<u32>> = vec![Vec::new(); truth.rule.len()];
    for s in 0..truth.rule.len() {
        if !mine[s] || is_cut(em.an, s) {
            continue;
        }
        let rule = &spec.rules[truth.rule[s] as usize];
        let env: Vec<u32> = rule
            .vars
            .iter()
            .map(|&(_, so)| gl.g.var(so, false))
            .collect();
        for (p, &r) in rule.premises.iter().zip(&truth.refs[s]) {
            let inst = instantiate(&mut gl.g, p, &env);
            let r = input.canon[r as usize] as usize;
            if is_cut(em.an, r) {
                uses[s].push(inst);
                cuts.push((inst, truth.judgment[r]));
            } else {
                uses[s].push(NONE);
                gl.g.unify(spec, inst, gl.judgment[r])?;
            }
        }
        gl.judgment[s] = instantiate(&mut gl.g, &rule.conclusion, &env);
    }
    let target = match open {
        Some(chosen) => {
            let class = &classes[*c as usize];
            let mut any = false;
            let t = gl.lower_pattern(em.an, class.conclusion, &mut |gl, k| match values.get(&k) {
                Some(_) if chosen.contains(&k) => {
                    any = true;
                    gl.eigen
                }
                // Other variables are left to the proof; what it leaves open
                // takes the ground value when settling.
                Some(&v) => {
                    gl.g.var(em.an.output[em.an.ground.node(v)[0] as usize], false)
                }
                None => gl.g.var(sort, false),
            });
            if !any {
                return Err("nothing to abstract".into());
            }
            t
        }
        None => gl.lower(em.an, truth.judgment[*root as usize]),
    };
    gl.g.unify(spec, gl.judgment[*root as usize], target)
        .map_err(|_| format!("goal {name}: its proof pins an abstracted variable"))?;

    // Choose open functional outputs, repeating while that settles more.
    let eigen = em.eigen;
    let mut pending = cuts.clone();
    loop {
        let before = pending.len();
        let mut rest = Vec::new();
        for &(use_node, ground_judgment) in &pending {
            let node = gl.g.find(use_node);
            let pred = gl.g.head[node as usize];
            let arity = spec.inputs[pred as usize].len();
            let args = gl.g.args(node, arity).to_vec();
            let memo = &mut Map::default();
            let raised: Vec<Option<u32>> = args
                .iter()
                .map(|&a| gl.raise(em.an, a, eigen, memo, 0))
                .collect();
            let outputs = &input.cut[&pred];
            let open: Vec<usize> = (0..arity).filter(|&i| raised[i].is_none()).collect();
            if open.is_empty() {
                continue;
            }
            if open.len() != 1 || !outputs.contains(&open[0]) {
                rest.push((use_node, ground_judgment));
                continue;
            }
            let out = open[0];
            let ground_out = em.an.ground.node(ground_judgment)[out + 1];
            let inputs = &spec.inputs[pred as usize];
            let mut candidates: Vec<u32> = (0..arity)
                .filter(|&i| i != out && inputs[i] == inputs[out])
                .filter_map(|i| raised[i])
                .collect();
            candidates.push(em.an.lift(ground_out));
            let mut chosen = None;
            for cand in candidates {
                let mut key = vec![pred];
                key.extend((0..arity).map(|i| if i == out { cand } else { raised[i].unwrap() }));
                let j = em.an.pat.intern(&key);
                if em.prove(j, 0).is_ok() {
                    chosen = Some(cand);
                    break;
                }
            }
            match chosen {
                Some(cand) => {
                    let x = gl.lower_pattern(em.an, cand, &mut |gl, _| gl.eigen);
                    gl.g.unify(spec, args[out], x)?;
                }
                None => rest.push((use_node, ground_judgment)),
            }
        }
        pending = rest;
        if pending.len() == before {
            break;
        }
    }
    let mut seen = Set::default();
    for (s, _) in mine.iter().enumerate().filter(|(_, m)| **m) {
        if !is_cut(em.an, s) {
            gl.settle(em.an, gl.judgment[s], truth.judgment[s], &mut seen);
        }
    }
    for &(node, g) in &cuts {
        gl.settle(em.an, node, g, &mut seen);
    }

    let mut index = vec![NONE; truth.rule.len()];
    let memo = &mut Map::default();
    for s in 0..truth.rule.len() {
        if !mine[s] || is_cut(em.an, s) {
            continue;
        }
        let j = gl
            .raise(em.an, gl.judgment[s], eigen, memo, 0)
            .ok_or("unsettled variable")?;
        if let Some(&n) = em.derived.get(&j) {
            index[s] = n;
            continue;
        }
        let mut refs = Vec::new();
        for (&r, &u) in truth.refs[s].iter().zip(&uses[s]) {
            refs.push(if u == NONE {
                index[input.canon[r as usize] as usize]
            } else {
                let c = gl
                    .raise(em.an, u, eigen, memo, 0)
                    .ok_or("unsettled variable")?;
                em.prove(c, 0)?
            });
        }
        let rule = spec.rules[truth.rule[s] as usize].name.clone();
        index[s] = em.step(&rule, &refs, j);
        em.derived.insert(j, index[s]);
    }
    let j = gl
        .raise(em.an, gl.judgment[*root as usize], eigen, memo, 0)
        .ok_or("unsettled goal")?;
    Ok((index[*root as usize], j))
}
