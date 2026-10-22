//! Untrusted oracle certificates, after Necula and Rahul's oracle-based
//! checking. Nothing here is part of the trusted boundary: decoding produces
//! an ordinary compact certificate, which the kernel checks step by step.
//!
//! A derivation is rebuilt top-down from the goals. Each subgoal is a
//! judgment that may still contain logic variables. A ground subgoal that was
//! already derived is reused at no cost. Otherwise the candidates are the
//! earlier judgments that unify with it (only for non-ground subgoals) and
//! the rules whose conclusion unifies with it; when there is more than one,
//! the oracle names the choice. Premises are solved ground-first, and a
//! conclusion that is still open after its premises takes witness terms from
//! the oracle. The oracle is the sequence of these decisions, coded with an
//! adaptive binary range coder whose contexts are the parent rule and premise
//! position, so a predictable decision costs a small fraction of a bit.
//!
//! The encoder runs the same reconstruction while reading each decision off a
//! known derivation, which keeps the two sides in step by construction.
use crate::lex::Lexer;
use crate::sexp::{Result, Sexp, parse, read};
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::io::{BufRead, Write};

const NONE: u32 = u32::MAX;
const PROP: u32 = u32::MAX;
const MAGIC: &[u8] = b"horn-oracle 1\n";
/// Version 2 records how many rules and constructor/predicate names the
/// theory had when the oracle was encoded. Decoding against a theory that
/// appends declarations then considers only that prefix, so extending the
/// theory does not invalidate existing oracles.
const MAGIC2: &[u8] = b"horn-oracle 2\n";
/// Nesting limit for subgoals and witness terms, so a corrupt oracle that
/// keeps choosing recursive rules stops with an error.
const MAX_DEPTH: usize = 1 << 16;
const STACK_BYTES: usize = 1 << 30;

#[derive(Default, Clone, Copy)]
struct Fx(u64);

impl Hasher for Fx {
    fn write(&mut self, bytes: &[u8]) {
        bytes.iter().for_each(|&b| self.add(u64::from(b)));
    }
    fn write_u32(&mut self, n: u32) {
        self.add(u64::from(n));
    }
    fn write_u64(&mut self, n: u64) {
        self.add(n);
    }
    fn write_usize(&mut self, n: usize) {
        self.add(n as u64);
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

impl Fx {
    fn add(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}

type Map<K, V> = HashMap<K, V, BuildHasherDefault<Fx>>;

/// Mix a decision context or an index key into one word.
fn mix(parts: &[u64]) -> u64 {
    let mut h = Fx(0x9e37_79b9_7f4a_7c15);
    parts.iter().for_each(|&p| h.add(p));
    h.0
}

pub(crate) enum Pat {
    Var(usize),
    App(u32, Vec<Pat>),
}

pub(crate) struct Rule {
    pub(crate) name: String,
    pub(crate) vars: Vec<(String, u32)>,
    pub(crate) premises: Vec<Pat>,
    pub(crate) conclusion: Pat,
    /// Conclusion variables that premises do not determine; a compact step
    /// must bind them.
    pub(crate) free: Vec<usize>,
}

/// The theory as the reconstruction sees it; malformed theories are left
/// for the kernel to reject.
pub(crate) struct Spec {
    pub(crate) sorts: HashMap<String, u32>,
    pub(crate) ctors: HashMap<String, u32>,
    pub(crate) preds: HashMap<String, u32>,
    pub(crate) names: Vec<String>,
    pub(crate) inputs: Vec<Vec<u32>>,
    pub(crate) by_sort: Vec<Vec<u32>>,
    pub(crate) rules: Vec<Rule>,
    pub(crate) rule_ix: HashMap<String, u32>,
    pub(crate) by_pred: Vec<Vec<u32>>,
}

impl Spec {
    pub(crate) fn parse(source: &str) -> Result<Self> {
        let mut spec = Spec {
            sorts: HashMap::new(),
            ctors: HashMap::new(),
            preds: HashMap::new(),
            names: Vec::new(),
            inputs: Vec::new(),
            by_sort: Vec::new(),
            rules: Vec::new(),
            rule_ix: HashMap::new(),
            by_pred: Vec::new(),
        };
        for form in parse(source)? {
            let xs = form.list()?;
            match (xs.first().map(Sexp::atom).transpose()?, xs.len()) {
                (Some("sort"), 2) => {
                    let id = spec.sorts.len() as u32;
                    spec.sorts.insert(xs[1].atom()?.to_owned(), id);
                    spec.by_sort.push(Vec::new());
                }
                (Some(tag @ ("ctor" | "pred")), n) if n == 3 + usize::from(tag == "ctor") => {
                    let id = spec.names.len() as u32;
                    let sort = |x: &Sexp| -> Result<u32> {
                        let s = x.atom()?;
                        spec.sorts
                            .get(s)
                            .copied()
                            .ok_or(format!("unknown sort {s}"))
                    };
                    let inputs = xs[2].list()?.iter().map(sort).collect::<Result<_>>()?;
                    if tag == "ctor" {
                        let output = sort(&xs[3])?;
                        spec.by_sort[output as usize].push(id);
                        spec.ctors.insert(xs[1].atom()?.to_owned(), id);
                    } else {
                        spec.preds.insert(xs[1].atom()?.to_owned(), id);
                    }
                    spec.names.push(xs[1].atom()?.to_owned());
                    spec.inputs.push(inputs);
                    spec.by_pred.push(Vec::new());
                }
                (Some("rule"), 4) => {
                    let mut vars = Vec::new();
                    let premises = xs[2].list()?.iter();
                    let premises = premises.map(|p| spec.pattern(p, PROP, &mut vars));
                    let premises = premises.collect::<Result<Vec<_>>>()?;
                    let in_premises = vars.len();
                    let conclusion = spec.pattern(&xs[3], PROP, &mut vars)?;
                    let mut free = Vec::new();
                    used(&conclusion, &mut |v| {
                        if v >= in_premises && !free.contains(&v) {
                            free.push(v);
                        }
                    });
                    let Pat::App(pred, _) = conclusion else {
                        return Err("rule conclusion must be a judgment".into());
                    };
                    let id = spec.rules.len() as u32;
                    spec.by_pred[pred as usize].push(id);
                    spec.rule_ix.insert(xs[1].atom()?.to_owned(), id);
                    spec.rules.push(Rule {
                        name: xs[1].atom()?.to_owned(),
                        vars,
                        premises,
                        conclusion,
                        free,
                    });
                }
                _ => return Err(format!("invalid theory declaration: {form}")),
            }
        }
        Ok(spec)
    }

    /// Restrict the candidates to the first `rules` rules and `names`
    /// constructors and predicates, the theory an oracle was encoded against.
    fn restrict(&mut self, rules: usize, names: usize) -> Result<()> {
        if rules > self.rules.len() || names > self.names.len() {
            return Err("oracle was encoded against a larger theory".into());
        }
        for list in &mut self.by_pred {
            list.retain(|&r| (r as usize) < rules);
        }
        for list in &mut self.by_sort {
            list.retain(|&c| (c as usize) < names);
        }
        Ok(())
    }

    fn pattern(&self, x: &Sexp, sort: u32, vars: &mut Vec<(String, u32)>) -> Result<Pat> {
        let (head, args) = match x {
            Sexp::List(xs) if sort == PROP => {
                (self.pred(xs.first().ok_or("empty judgment")?)?, &xs[1..])
            }
            Sexp::Atom(v) if v.starts_with('?') => {
                let i = match vars.iter().position(|(n, _)| n == v) {
                    Some(i) => i,
                    None => {
                        vars.push((v.clone(), sort));
                        vars.len() - 1
                    }
                };
                return Ok(Pat::Var(i));
            }
            Sexp::Atom(c) => (self.ctor(c)?, &[][..]),
            Sexp::List(xs) => (
                self.ctor(xs.first().ok_or("empty term")?.atom()?)?,
                &xs[1..],
            ),
        };
        let inputs = &self.inputs[head as usize];
        if inputs.len() != args.len() {
            return Err(format!("arity mismatch: {x}"));
        }
        let args = args
            .iter()
            .zip(inputs)
            .map(|(a, &s)| self.pattern(a, s, vars));
        Ok(Pat::App(head, args.collect::<Result<_>>()?))
    }

    fn ctor(&self, c: &str) -> Result<u32> {
        self.ctors
            .get(c)
            .copied()
            .ok_or_else(|| format!("unknown constructor {c}"))
    }

    fn pred(&self, p: &Sexp) -> Result<u32> {
        let p = p.atom()?;
        self.preds
            .get(p)
            .copied()
            .ok_or_else(|| format!("unknown predicate {p}"))
    }

    pub(crate) fn rule(&self, name: &str) -> Result<u32> {
        self.rule_ix
            .get(name)
            .copied()
            .ok_or_else(|| format!("unknown rule {name}"))
    }
}

fn used(p: &Pat, f: &mut impl FnMut(usize)) {
    match p {
        Pat::Var(v) => f(*v),
        Pat::App(_, args) => args.iter().for_each(|a| used(a, f)),
    }
}

/// Hash-consed ground nodes `[head, args...]`, as in the kernel.
pub(crate) struct Store {
    data: Vec<u32>,
    starts: Vec<usize>,
    table: Vec<u32>,
    bits: u32,
}

impl Store {
    pub(crate) fn new() -> Self {
        Self {
            data: Vec::new(),
            starts: vec![0],
            table: vec![NONE; 1 << 10],
            bits: 10,
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.starts.len() - 1
    }

    pub(crate) fn node(&self, id: u32) -> &[u32] {
        let i = id as usize;
        &self.data[self.starts[i]..self.starts[i + 1]]
    }

    fn slot(&self, key: &[u32]) -> usize {
        let mut h = Fx(0);
        key.iter().for_each(|&x| h.add(u64::from(x)));
        (h.0 >> (64 - self.bits)) as usize
    }

    pub(crate) fn intern(&mut self, key: &[u32]) -> u32 {
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
                id if self.node(id) == key => return id,
                _ => i = (i + 1) & (self.table.len() - 1),
            }
        }
        let id = self.len() as u32;
        self.data.extend_from_slice(key);
        self.starts.push(self.data.len());
        self.table[i] = id;
        id
    }

    /// A ground term or judgment written in certificate syntax.
    fn read(
        &mut self,
        spec: &Spec,
        defs: &HashMap<String, u32>,
        x: &Sexp,
        sort: u32,
    ) -> Result<u32> {
        let (head, args) = match x {
            Sexp::List(xs) if sort == PROP => {
                (spec.pred(xs.first().ok_or("empty judgment")?)?, &xs[1..])
            }
            Sexp::Atom(a) if a.starts_with('?') => {
                return defs
                    .get(a)
                    .copied()
                    .ok_or_else(|| format!("undefined abbreviation {a}"));
            }
            Sexp::Atom(c) => (spec.ctor(c)?, &[][..]),
            Sexp::List(xs) => (
                spec.ctor(xs.first().ok_or("empty term")?.atom()?)?,
                &xs[1..],
            ),
        };
        let inputs = &spec.inputs[head as usize];
        if inputs.len() != args.len() {
            return Err(format!("arity mismatch: {x}"));
        }
        let mut key = vec![head];
        for (a, &s) in args.iter().zip(inputs) {
            key.push(self.read(spec, defs, a, s)?);
        }
        Ok(self.intern(&key))
    }

    pub(crate) fn matches(&self, p: &Pat, id: u32, env: &mut [u32]) -> bool {
        match p {
            Pat::Var(v) if env[*v] == NONE => {
                env[*v] = id;
                true
            }
            Pat::Var(v) => env[*v] == id,
            Pat::App(head, args) => {
                let node = self.node(id);
                node[0] == *head
                    && node.len() == args.len() + 1
                    && args
                        .iter()
                        .enumerate()
                        .all(|(k, a)| self.matches(a, self.node(id)[k + 1], env))
            }
        }
    }

    pub(crate) fn build(&mut self, p: &Pat, env: &[u32]) -> Result<u32> {
        match p {
            Pat::Var(v) if env[*v] == NONE => Err("unbound conclusion variable".into()),
            Pat::Var(v) => Ok(env[*v]),
            Pat::App(head, args) => {
                let mut key = vec![*head];
                for a in args {
                    key.push(self.build(a, env)?);
                }
                Ok(self.intern(&key))
            }
        }
    }
}

/// LZMA-style adaptive binary range coder with 11-bit probabilities.
struct Encoder {
    low: u64,
    range: u32,
    cache: u8,
    pending: u64,
    out: Vec<u8>,
}

impl Encoder {
    fn bit(&mut self, p: &mut u16, bit: bool) {
        let bound = (self.range >> 11) * u32::from(*p);
        if bit {
            self.low += u64::from(bound);
            self.range -= bound;
            *p -= *p >> 5;
        } else {
            self.range = bound;
            *p += (2048 - *p) >> 5;
        }
        while self.range < 1 << 24 {
            self.range <<= 8;
            self.shift();
        }
    }

    fn shift(&mut self) {
        if (self.low as u32) < 0xff00_0000 || self.low >> 32 != 0 {
            let carry = (self.low >> 32) as u8;
            let mut byte = self.cache;
            while self.pending > 0 {
                self.out.push(byte.wrapping_add(carry));
                byte = 0xff;
                self.pending -= 1;
            }
            self.cache = (self.low >> 24) as u8;
        }
        self.pending += 1;
        self.low = (self.low & 0x00ff_ffff) << 8;
    }

    fn finish(mut self) -> Vec<u8> {
        for _ in 0..5 {
            self.shift();
        }
        self.out
    }
}

struct Decoder<'a> {
    input: &'a [u8],
    pos: usize,
    code: u32,
    range: u32,
}

impl Decoder<'_> {
    fn byte(&mut self) -> Result<u8> {
        self.pos += 1;
        match self.input.get(self.pos - 1) {
            Some(&b) => Ok(b),
            // The encoder's final flush can leave the decoder a few bytes
            // short; reading far past the end means the oracle is truncated
            // or is driving an unbounded reconstruction.
            None if self.pos <= self.input.len() + 8 => Ok(0),
            None => Err("oracle exhausted".into()),
        }
    }

    fn bit(&mut self, p: &mut u16) -> Result<bool> {
        let bound = (self.range >> 11) * u32::from(*p);
        let bit = self.code >= bound;
        if bit {
            self.code -= bound;
            self.range -= bound;
            *p -= *p >> 5;
        } else {
            self.range = bound;
            *p += (2048 - *p) >> 5;
        }
        while self.range < 1 << 24 {
            self.range <<= 8;
            self.code = (self.code << 8) | u32::from(self.byte()?);
        }
        Ok(bit)
    }
}

enum Coder<'a> {
    Encode(Encoder),
    Decode(Decoder<'a>),
}

/// The known derivation the encoder reads decisions from.
pub(crate) struct Truth {
    pub(crate) rule: Vec<u32>,
    pub(crate) refs: Vec<Vec<u32>>,
    pub(crate) judgment: Vec<u32>,
    pub(crate) results: HashMap<String, u32>,
}

/// A term during reconstruction: ground (hash-consed), a logic variable, or
/// a compound with at least one non-ground argument.
#[derive(Clone, Copy, PartialEq, Eq)]
enum T {
    G(u32),
    V(u32),
    S(u32),
}

struct Compound {
    head: u32,
    start: u32,
    len: u32,
    /// Ground id once every argument is ground; set only outside trials.
    ground: u32,
}

struct Output<'w> {
    w: Box<dyn Write + Send + 'w>,
    defs: Map<u32, String>,
}

#[derive(Debug, Default)]
pub struct Stats {
    pub goals: usize,
    /// Steps of the reconstructed compact certificate.
    pub steps: usize,
    /// Binary decisions coded, including ones the model predicts well.
    pub decisions: usize,
    /// Witness terms supplied for conclusions left open by their premises.
    pub witnesses: usize,
    /// Deepest subgoal nesting reached.
    pub depth: usize,
    pub oracle_bytes: usize,
}

struct Engine<'s, 'w> {
    spec: &'s Spec,
    store: Store,
    vars: Vec<(Option<T>, u32)>,
    compounds: Vec<Compound>,
    args: Vec<T>,
    trail: Vec<u32>,
    /// Derived judgment -> step number.
    done: Map<u32, u32>,
    /// Derived judgments per predicate, in derivation order.
    derived: Vec<Vec<u32>>,
    /// Argument-position masks indexed so far for each predicate.
    masks: Vec<Vec<u64>>,
    buckets: Map<u64, Vec<u32>>,
    model: Map<u64, u16>,
    coder: Coder<'w>,
    truth: Option<Truth>,
    out: Option<Output<'w>>,
    stats: Stats,
}

impl<'s, 'w> Engine<'s, 'w> {
    fn new(spec: &'s Spec, store: Store, coder: Coder<'w>) -> Self {
        Self {
            spec,
            store,
            vars: Vec::new(),
            compounds: Vec::new(),
            args: Vec::new(),
            trail: Vec::new(),
            done: Map::default(),
            derived: vec![Vec::new(); spec.names.len()],
            masks: vec![Vec::new(); spec.names.len()],
            buckets: Map::default(),
            model: Map::default(),
            coder,
            truth: None,
            out: None,
            stats: Stats::default(),
        }
    }

    fn bit(&mut self, ctx: u64, value: bool) -> Result<bool> {
        self.stats.decisions += 1;
        let p = self.model.entry(ctx).or_insert(1024);
        match &mut self.coder {
            Coder::Encode(e) => {
                e.bit(p, value);
                Ok(value)
            }
            Coder::Decode(d) => d.bit(p),
        }
    }

    /// Pick one of `ctxs.len()` candidates by asking, in order, "is it this
    /// one?"; `chosen` is only read when encoding.
    fn choose(&mut self, chosen: usize, ctxs: &[u64]) -> Result<usize> {
        for (i, &ctx) in ctxs.iter().enumerate().take(ctxs.len() - 1) {
            if self.bit(ctx, chosen == i)? {
                return Ok(i);
            }
        }
        Ok(ctxs.len() - 1)
    }

    fn deref(&self, mut t: T) -> T {
        while let T::V(v) = t {
            match self.vars[v as usize].0 {
                Some(b) => t = b,
                None => break,
            }
        }
        t
    }

    fn arg(&self, t: T, k: usize) -> T {
        match t {
            T::G(g) => T::G(self.store.node(g)[k + 1]),
            T::S(s) => self.args[self.compounds[s as usize].start as usize + k],
            T::V(_) => unreachable!("arguments of a variable"),
        }
    }

    fn head(&self, t: T) -> Option<(u32, usize)> {
        match t {
            T::G(g) => Some((self.store.node(g)[0], self.store.node(g).len() - 1)),
            T::S(s) => {
                let c = &self.compounds[s as usize];
                Some((c.head, c.len as usize))
            }
            T::V(_) => None,
        }
    }

    fn ground(&mut self, t: T) -> Option<u32> {
        match self.deref(t) {
            T::G(g) => Some(g),
            T::V(_) => None,
            T::S(s) => {
                let c = &self.compounds[s as usize];
                if c.ground != NONE {
                    return Some(c.ground);
                }
                let (head, start, len) = (c.head, c.start as usize, c.len as usize);
                let mut key = Vec::with_capacity(len + 1);
                key.push(head);
                for k in 0..len {
                    key.push(self.ground(self.args[start + k])?);
                }
                let id = self.store.intern(&key);
                self.compounds[s as usize].ground = id;
                Some(id)
            }
        }
    }

    fn compound(&mut self, head: u32, args: &[T]) -> T {
        if args.iter().all(|a| matches!(a, T::G(_))) {
            let mut key = vec![head];
            key.extend(args.iter().map(|a| match a {
                T::G(g) => *g,
                _ => unreachable!(),
            }));
            return T::G(self.store.intern(&key));
        }
        self.compounds.push(Compound {
            head,
            start: self.args.len() as u32,
            len: args.len() as u32,
            ground: NONE,
        });
        self.args.extend_from_slice(args);
        T::S(self.compounds.len() as u32 - 1)
    }

    fn fresh(&mut self, sort: u32) -> T {
        self.vars.push((None, sort));
        T::V(self.vars.len() as u32 - 1)
    }

    fn inst(&mut self, p: &Pat, env: &mut [Option<T>], vars: &[(String, u32)]) -> T {
        match p {
            Pat::Var(v) => match env[*v] {
                Some(t) => t,
                None => {
                    let t = self.fresh(vars[*v].1);
                    env[*v] = Some(t);
                    t
                }
            },
            Pat::App(head, ps) => {
                let args: Vec<T> = ps.iter().map(|p| self.inst(p, env, vars)).collect();
                self.compound(*head, &args)
            }
        }
    }

    fn bind(&mut self, v: u32, t: T) {
        self.vars[v as usize].0 = Some(t);
        self.trail.push(v);
    }

    fn occurs(&self, v: u32, t: T) -> bool {
        match self.deref(t) {
            T::V(w) => v == w,
            T::G(_) => false,
            T::S(s) => {
                let c = &self.compounds[s as usize];
                (0..c.len as usize).any(|k| self.occurs(v, self.args[c.start as usize + k]))
            }
        }
    }

    fn unify(&mut self, a: T, b: T) -> bool {
        let (a, b) = (self.deref(a), self.deref(b));
        match (a, b) {
            _ if a == b => true,
            (T::V(v), t) | (t, T::V(v)) => {
                if self.occurs(v, t) {
                    return false;
                }
                self.bind(v, t);
                true
            }
            (T::G(_), T::G(_)) => false,
            _ => {
                let (ha, hb) = (self.head(a), self.head(b));
                ha == hb
                    && (0..ha.map_or(0, |h| h.1))
                        .all(|k| self.unify(self.arg(a, k), self.arg(b, k)))
            }
        }
    }

    fn unify_pat(&mut self, p: &Pat, env: &mut [Option<T>], vars: &[(String, u32)], t: T) -> bool {
        match p {
            Pat::Var(v) => match env[*v] {
                Some(x) => self.unify(x, t),
                None => {
                    env[*v] = Some(t);
                    true
                }
            },
            Pat::App(head, ps) => match self.deref(t) {
                T::V(_) => {
                    let x = self.inst(p, env, vars);
                    self.unify(x, t)
                }
                t => {
                    let (h, n) = self.head(t).expect("not a variable");
                    h == *head
                        && n == ps.len()
                        && ps
                            .iter()
                            .enumerate()
                            .all(|(k, p)| self.unify_pat(p, env, vars, self.arg(t, k)))
                }
            },
        }
    }

    fn mark(&self) -> (usize, usize, usize) {
        (self.vars.len(), self.compounds.len(), self.args.len())
    }

    fn release(&mut self, (v, c, a): (usize, usize, usize)) {
        self.vars.truncate(v);
        self.compounds.truncate(c);
        self.args.truncate(a);
    }

    /// Run `f` as a trial: every binding and allocation is undone afterwards.
    /// Trials never nest, so the trail only matters inside one.
    fn trial(&mut self, f: impl FnOnce(&mut Self) -> bool) -> bool {
        self.trail.clear();
        let mark = self.mark();
        let ok = f(self);
        for v in self.trail.drain(..) {
            if (v as usize) < mark.0 {
                self.vars[v as usize].0 = None;
            }
        }
        self.release(mark);
        ok
    }

    /// After a premise is solved its term is ground. Rebind every variable it
    /// reaches, through any chain of bindings, to a ground id, so nothing
    /// older than the premise's derivation points into what it allocated and
    /// that can be released.
    fn settle(&mut self, t: T) {
        match t {
            T::G(_) => {}
            T::V(v) => {
                if let Some(b) = self.vars[v as usize].0
                    && !matches!(b, T::G(_))
                {
                    self.settle(b);
                    if let Some(g) = self.ground(b) {
                        self.vars[v as usize].0 = Some(T::G(g));
                    }
                }
            }
            // A cached ground id does not help: the variables inside may still
            // be bound to what the premise's derivation allocated.
            T::S(s) => {
                let c = &self.compounds[s as usize];
                let (start, len) = (c.start as usize, c.len as usize);
                for k in 0..len {
                    self.settle(self.args[start + k]);
                }
                self.ground(t);
            }
        }
    }

    fn unbound(&self, t: T, out: &mut Vec<u32>) {
        match self.deref(t) {
            T::V(v) if !out.contains(&v) => out.push(v),
            T::S(s) => {
                let c = &self.compounds[s as usize];
                for k in 0..c.len as usize {
                    self.unbound(self.args[c.start as usize + k], out);
                }
            }
            _ => {}
        }
    }

    fn index_key(&self, pred: u32, mask: u64, args: &[u32]) -> u64 {
        let mut h = Fx(mix(&[u64::from(pred), mask]));
        (0..args.len().min(64))
            .filter(|k| mask >> k & 1 == 1)
            .for_each(|k| h.add(u64::from(args[k])));
        h.0
    }

    /// Earlier judgments that unify with a non-ground goal, in derivation order.
    fn lookup(&mut self, goal: T, pred: u32, arity: usize) -> Vec<u32> {
        let mut mask = 0u64;
        let mut key = vec![NONE; arity];
        for (k, slot) in key.iter_mut().enumerate().take(64) {
            if let Some(g) = self.ground(self.arg(goal, k)) {
                mask |= 1 << k;
                *slot = g;
            }
        }
        let p = pred as usize;
        if !self.masks[p].contains(&mask) {
            self.masks[p].push(mask);
            for i in 0..self.derived[p].len() {
                let j = self.derived[p][i];
                let k = self.index_key(pred, mask, &self.store.node(j)[1..]);
                self.buckets.entry(k).or_default().push(j);
            }
        }
        let k = self.index_key(pred, mask, &key);
        let bucket = self.buckets.get(&k).cloned().unwrap_or_default();
        bucket
            .into_iter()
            .filter(|&j| self.trial(|e| e.unify(goal, T::G(j))))
            .collect()
    }

    fn remember(&mut self, judgment: u32, step: u32) {
        self.done.insert(judgment, step);
        let pred = self.store.node(judgment)[0];
        self.derived[pred as usize].push(judgment);
        for i in 0..self.masks[pred as usize].len() {
            let mask = self.masks[pred as usize][i];
            let k = self.index_key(pred, mask, &self.store.node(judgment)[1..]);
            self.buckets.entry(k).or_default().push(judgment);
        }
    }

    /// Derive `goal`, returning its step number. `truth` is the step of the
    /// known derivation when encoding and `NONE` when decoding.
    fn solve(&mut self, goal: T, truth: u32, parent: u64, depth: usize) -> Result<u32> {
        if depth > MAX_DEPTH {
            return Err("reconstruction nesting exceeds its limit".into());
        }
        self.stats.depth = self.stats.depth.max(depth);
        let spec = self.spec;
        let ground = self.ground(goal);
        if let Some(n) = ground.and_then(|g| self.done.get(&g)) {
            return Ok(*n);
        }
        let goal = self.deref(goal);
        let (pred, arity) = self.head(goal).ok_or("a goal must be a judgment")?;
        let reuse = match ground {
            Some(_) => Vec::new(),
            None => self.lookup(goal, pred, arity),
        };
        let mut rules = Vec::new();
        for &r in &spec.by_pred[pred as usize] {
            let rule = &spec.rules[r as usize];
            let mut env = vec![None; rule.vars.len()];
            if self.trial(|e| e.unify_pat(&rule.conclusion, &mut env, &rule.vars, goal)) {
                rules.push(r);
            }
        }
        let chosen = match &self.truth {
            None => 0,
            Some(t) => {
                let j = t.judgment[truth as usize];
                let diverged = || format!("certificate step {truth} does not fit its use");
                if ground.is_none() && self.done.contains_key(&j) {
                    reuse.iter().position(|&x| x == j).ok_or_else(diverged)?
                } else {
                    let r = t.rule[truth as usize];
                    reuse.len() + rules.iter().position(|&x| x == r).ok_or_else(diverged)?
                }
            }
        };
        let open = u64::from(ground.is_none());
        let ctxs: Vec<u64> = (0..reuse.len())
            .map(|i| mix(&[1, parent, open, i.min(7) as u64]))
            .chain(rules.iter().map(|&r| mix(&[2, parent, open, u64::from(r)])))
            .collect();
        if ctxs.is_empty() {
            return Err(format!(
                "no rule derives a goal for {}",
                spec.names[pred as usize]
            ));
        }
        let c = self.choose(chosen, &ctxs)?;
        if let Some(&j) = reuse.get(c) {
            self.unify(goal, T::G(j));
            return Ok(self.done[&j]);
        }
        let r = rules[c - reuse.len()];
        let rule = &spec.rules[r as usize];
        let mut env = vec![None; rule.vars.len()];
        self.unify_pat(&rule.conclusion, &mut env, &rule.vars, goal);
        let premises: Vec<T> = rule
            .premises
            .iter()
            .map(|p| self.inst(p, &mut env, &rule.vars))
            .collect();
        let mut refs = vec![NONE; premises.len()];
        let mut todo: Vec<usize> = (0..premises.len()).collect();
        while !todo.is_empty() {
            let next = (0..todo.len()).find(|&i| self.ground(premises[todo[i]]).is_some());
            let k = todo.remove(next.unwrap_or(0));
            let below = match &self.truth {
                Some(t) => t.refs[truth as usize][k],
                None => NONE,
            };
            let mark = self.mark();
            let context = mix(&[3, u64::from(r), k as u64]);
            refs[k] = self.solve(premises[k], below, context, depth + 1)?;
            self.settle(premises[k]);
            self.release(mark);
        }
        let mut open = Vec::new();
        self.unbound(goal, &mut open);
        if !open.is_empty() {
            if let Some(t) = &self.truth {
                let j = t.judgment[truth as usize];
                if !self.unify(goal, T::G(j)) {
                    return Err(format!("certificate step {truth} does not fit its use"));
                }
            }
            for (w, &v) in open.iter().enumerate() {
                let value = self.ground(T::V(v));
                let sort = self.vars[v as usize].1;
                let id = self.term(sort, value, mix(&[4, u64::from(r), w.min(7) as u64]), depth)?;
                if value.is_none() {
                    self.bind(v, T::G(id));
                }
                self.stats.witnesses += 1;
            }
        }
        let judgment = self.ground(goal).ok_or("conclusion is not ground")?;
        if let Some(t) = &self.truth
            && judgment != t.judgment[truth as usize]
        {
            return Err(format!("certificate step {truth} does not fit its use"));
        }
        let step = self.stats.steps as u32;
        self.stats.steps += 1;
        if self.out.is_some() {
            let mut bindings = String::new();
            for &v in &rule.free {
                let id = self
                    .ground(env[v].expect("conclusion variable"))
                    .expect("ground");
                let text = self.write_term(id)?;
                bindings.push_str(&format!(" ({} {text})", rule.vars[v].0));
            }
            let refs: Vec<String> = refs.iter().map(u32::to_string).collect();
            let line = format!(
                "(step {step} {} ({}){bindings})\n",
                rule.name,
                refs.join(" ")
            );
            self.emit(&line)?;
        }
        self.remember(judgment, step);
        Ok(step)
    }

    /// A witness term of `sort`, constructor by constructor; `value` is read
    /// only when encoding.
    fn term(&mut self, sort: u32, value: Option<u32>, ctx: u64, depth: usize) -> Result<u32> {
        if depth > MAX_DEPTH {
            return Err("witness nesting exceeds its limit".into());
        }
        let spec = self.spec;
        let ctors = &spec.by_sort[sort as usize];
        if ctors.is_empty() {
            return Err("witness of an empty sort".into());
        }
        let chosen = match value {
            Some(id) => ctors
                .iter()
                .position(|&c| c == self.store.node(id)[0])
                .ok_or("ill-sorted witness")?,
            None => 0,
        };
        let ctxs: Vec<u64> = ctors
            .iter()
            .map(|&c| mix(&[5, ctx, u64::from(c)]))
            .collect();
        let c = ctors[self.choose(chosen, &ctxs)?];
        let mut key = vec![c];
        for (k, &s) in spec.inputs[c as usize].iter().enumerate() {
            let v = value.map(|id| self.store.node(id)[k + 1]);
            key.push(self.term(s, v, mix(&[6, u64::from(c), k as u64]), depth + 1)?);
        }
        Ok(self.store.intern(&key))
    }

    fn emit(&mut self, text: &str) -> Result<()> {
        let out = self.out.as_mut().expect("output");
        out.w.write_all(text.as_bytes()).map_err(|e| e.to_string())
    }

    /// Certificate text for a ground term; every compound is written once as
    /// a `def`, before the line that first uses it.
    fn write_term(&mut self, id: u32) -> Result<String> {
        let node = self.store.node(id);
        if node.len() == 1 {
            return Ok(self.spec.names[node[0] as usize].clone());
        }
        if let Some(name) = self.out.as_ref().and_then(|o| o.defs.get(&id)) {
            return Ok(name.clone());
        }
        let mut text = format!("({}", self.spec.names[node[0] as usize]);
        for k in 1..node.len() {
            let arg = self.store.node(id)[k];
            text.push(' ');
            text.push_str(&self.write_term(arg)?);
        }
        let out = self.out.as_mut().expect("output");
        let name = format!("?{}", out.defs.len());
        out.defs.insert(id, name.clone());
        self.emit(&format!("(def {name} {text}))\n"))?;
        Ok(name)
    }

    fn run(&mut self, goals: &[(String, u32)]) -> Result<()> {
        for (name, judgment) in goals {
            let truth = match &self.truth {
                Some(t) => *t
                    .results
                    .get(name)
                    .ok_or_else(|| format!("no result for goal {name}"))?,
                None => NONE,
            };
            let pred = self.store.node(*judgment)[0];
            let mark = self.mark();
            let step = self.solve(T::G(*judgment), truth, mix(&[0, u64::from(pred)]), 0)?;
            self.release(mark);
            if self.out.is_some() {
                self.emit(&format!("(result {name} {step})\n"))?;
            }
        }
        self.stats.goals = goals.len();
        if let Some(out) = &mut self.out {
            out.w.flush().map_err(|e| e.to_string())?;
        }
        Ok(())
    }
}

pub(crate) fn read_goals(
    spec: &Spec,
    store: &mut Store,
    source: &str,
) -> Result<Vec<(String, u32)>> {
    let mut goals = Vec::new();
    for form in parse(source)? {
        let xs = form.list()?;
        if xs.len() != 3 || xs[0].atom()? != "goal" {
            return Err("expected (goal name judgment)".into());
        }
        goals.push((
            xs[1].atom()?.to_owned(),
            store.read(spec, &HashMap::new(), &xs[2], PROP)?,
        ));
    }
    Ok(goals)
}

/// Read an ordinary or compact certificate and work out every step's
/// judgment. The certificate is not validated beyond what that needs.
pub(crate) fn read_truth(spec: &Spec, store: &mut Store, proof: impl BufRead) -> Result<Truth> {
    let mut truth = Truth {
        rule: Vec::new(),
        refs: Vec::new(),
        judgment: Vec::new(),
        results: HashMap::new(),
    };
    let mut defs = HashMap::new();
    let lexer = &mut Lexer::new(proof);
    let index =
        |x: &Sexp| -> Result<u32> { x.atom()?.parse().map_err(|_| "bad step index".into()) };
    while lexer.peek()?.is_some() {
        let form = read(lexer, 0)?;
        let xs = form.list()?;
        match (xs.first().map(Sexp::atom).transpose()?, xs.len()) {
            (Some("step"), n) if n >= 4 => {
                if index(&xs[1])? as usize != truth.rule.len() {
                    return Err("steps must be numbered consecutively".into());
                }
                let r = spec.rule(xs[2].atom()?)?;
                let rule = &spec.rules[r as usize];
                let refs = xs[3]
                    .list()?
                    .iter()
                    .map(index)
                    .collect::<Result<Vec<_>>>()?;
                if refs.len() != rule.premises.len() {
                    return Err("wrong number of premises".into());
                }
                let mut env = vec![NONE; rule.vars.len()];
                for (p, &n) in rule.premises.iter().zip(&refs) {
                    let fact = *truth
                        .judgment
                        .get(n as usize)
                        .ok_or("premise is not an earlier step")?;
                    if !store.matches(p, fact, &mut env) {
                        return Err("premise mismatch".into());
                    }
                }
                let mut stated = None;
                for item in &xs[4..] {
                    let ys = item.list()?;
                    match ys.first().map(Sexp::atom).transpose()? {
                        Some(v) if v.starts_with('?') && ys.len() == 2 => {
                            let i = rule
                                .vars
                                .iter()
                                .position(|(n, _)| n == v)
                                .ok_or("unknown variable")?;
                            let value = store.read(spec, &defs, &ys[1], rule.vars[i].1)?;
                            if !store.matches(&Pat::Var(i), value, &mut env) {
                                return Err("conflicting binding".into());
                            }
                        }
                        _ => stated = Some(store.read(spec, &defs, item, PROP)?),
                    }
                }
                let judgment = match stated {
                    Some(j) if store.matches(&rule.conclusion, j, &mut env) => j,
                    Some(_) => return Err("conclusion mismatch".into()),
                    None => store.build(&rule.conclusion, &env)?,
                };
                truth.rule.push(r);
                truth.refs.push(refs);
                truth.judgment.push(judgment);
            }
            (Some("def"), 3) => {
                // Any declared sort reads a term; only judgments differ.
                let value = store.read(spec, &defs, &xs[2], 0)?;
                defs.insert(xs[1].atom()?.to_owned(), value);
            }
            (Some("result"), 3) => {
                let n = index(&xs[2])?;
                if n as usize >= truth.rule.len() {
                    return Err("result refers to a missing step".into());
                }
                truth.results.insert(xs[1].atom()?.to_owned(), n);
            }
            _ => return Err(format!("unsupported proof form: {form}")),
        }
    }
    Ok(truth)
}

/// Run `f` on a thread whose stack fits deep reconstructions.
pub(crate) fn deep<R: Send>(f: impl FnOnce() -> Result<R> + Send) -> Result<R> {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(STACK_BYTES)
            .spawn_scoped(s, f)
            .map_err(|e| e.to_string())?
            .join()
            .map_err(|_| "reconstruction thread panicked".to_string())?
    })
}

/// Encode the decisions that rebuild a derivation of `goals` from `proof`,
/// an ordinary or compact certificate. Steps no goal needs are left out.
pub fn encode(theory: &str, goals: &str, proof: impl BufRead + Send) -> Result<(Vec<u8>, Stats)> {
    deep(|| {
        let spec = Spec::parse(theory)?;
        let mut store = Store::new();
        let goals = read_goals(&spec, &mut store, goals)?;
        let truth = read_truth(&spec, &mut store, proof)?;
        let encoder = Encoder {
            low: 0,
            range: u32::MAX,
            cache: 0,
            pending: 1,
            out: Vec::new(),
        };
        let mut engine = Engine::new(&spec, store, Coder::Encode(encoder));
        engine.truth = Some(truth);
        engine.run(&goals)?;
        let Coder::Encode(encoder) = engine.coder else {
            unreachable!()
        };
        let mut bytes = MAGIC2.to_vec();
        bytes.extend((spec.rules.len() as u32).to_le_bytes());
        bytes.extend((spec.names.len() as u32).to_le_bytes());
        bytes.extend(encoder.finish());
        engine.stats.oracle_bytes = bytes.len();
        Ok((bytes, engine.stats))
    })
}

/// Rebuild the compact certificate an oracle describes and write it to `out`.
/// The result proves nothing until the kernel has checked it.
pub fn decode(theory: &str, goals: &str, oracle: &[u8], out: impl Write + Send) -> Result<Stats> {
    deep(|| {
        let mut spec = Spec::parse(theory)?;
        let input = if let Some(input) = oracle.strip_prefix(MAGIC) {
            input
        } else {
            let input = oracle.strip_prefix(MAGIC2).ok_or("not a Horn oracle")?;
            let (counts, input) = input.split_at_checked(8).ok_or("truncated oracle header")?;
            let count = |i: usize| u32::from_le_bytes(counts[i..i + 4].try_into().unwrap());
            spec.restrict(count(0) as usize, count(4) as usize)?;
            input
        };
        let mut store = Store::new();
        let goals = read_goals(&spec, &mut store, goals)?;
        let mut decoder = Decoder {
            input,
            pos: 0,
            code: 0,
            range: u32::MAX,
        };
        for _ in 0..5 {
            decoder.code = (decoder.code << 8) | u32::from(decoder.byte()?);
        }
        let mut engine = Engine::new(&spec, store, Coder::Decode(decoder));
        engine.out = Some(Output {
            w: Box::new(out),
            defs: Map::default(),
        });
        engine.run(&goals)?;
        engine.stats.oracle_bytes = oracle.len();
        Ok(engine.stats)
    })
}

/// Decode an untrusted oracle into a pipe and check every emitted step with
/// the ground kernel against the caller's theory and exact goals. No decoded
/// proof file is materialized, and decoder failure is never acceptance.
pub fn check(theory: &str, goals: &str, oracle: &[u8]) -> Result<crate::kernel::Report> {
    Ok(check_with_rules(theory, goals, oracle)?.0)
}

/// Passes decoded text through, collecting the rule named by each step line.
struct RuleScan<W> {
    inner: W,
    line: Vec<u8>,
    /// Spaces in `line`.
    spaces: usize,
    rules: std::collections::BTreeSet<String>,
}

impl<W: Write> RuleScan<W> {
    /// Whether the line read so far may still end inside the rule name of
    /// `(step N RULE ...)`: it is a prefix of `(step ` or starts with it,
    /// and the space after the rule name has not been read yet.
    fn wants_more(&self) -> bool {
        const STEP: &[u8] = b"(step ";
        let start = self.line.len().min(STEP.len());
        self.line[..start] == STEP[..start] && self.spaces < 3
    }

    fn scan(&mut self) {
        if let Some(rest) = self.line.strip_prefix(b"(step ")
            && let Some(rule) = rest.split(|b| *b == b' ').nth(1)
            && let Ok(rule) = std::str::from_utf8(rule)
            && !self.rules.contains(rule)
        {
            self.rules.insert(rule.to_owned());
        }
        self.line.clear();
        self.spaces = 0;
    }
}

impl<W: Write> Write for RuleScan<W> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let n = self.inner.write(buf)?;
        for &b in &buf[..n] {
            if b == b'\n' {
                self.scan();
            } else if self.wants_more() {
                self.line.push(b);
                self.spaces += usize::from(b == b' ');
            }
        }
        Ok(n)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        self.inner.flush()
    }
}

/// `check`, also returning the sorted names of the rules used by the steps
/// the kernel accepted. The names are read from the decoded stream on its
/// way to the kernel, so the oracle is decoded once.
pub fn check_with_rules(
    theory: &str,
    goals: &str,
    oracle: &[u8],
) -> Result<(crate::kernel::Report, Vec<String>)> {
    check_text_with_rules(theory, goals, |out| {
        decode(theory, goals, oracle, out).map(drop)
    })
}

/// The pipe `check_text_with_rules` hands its writer: proof text written here
/// goes to the kernel, and the rule of each step line is noted on the way.
pub struct ProofSink(RuleScan<std::io::BufWriter<std::io::PipeWriter>>);

impl Write for ProofSink {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.write(buf)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        self.0.flush()
    }
}

/// Check the derivation that `write` streams as proof text with the ground
/// kernel against `theory` and the exact `goals`, also returning the sorted
/// names of the rules its accepted steps use. `write` runs on the calling
/// thread and the kernel reads its output through a pipe, so no proof file
/// is materialized; a writer failure is never acceptance.
pub fn check_text_with_rules(
    theory: &str,
    goals: &str,
    write: impl FnOnce(&mut ProofSink) -> Result<()>,
) -> Result<(crate::kernel::Report, Vec<String>)> {
    use std::io::{BufReader, BufWriter};
    let checker = crate::kernel::Theory::parse(theory)?;
    let (reader, writer) = std::io::pipe().map_err(|e| e.to_string())?;
    let (report, written) = std::thread::scope(|scope| {
        let kernel =
            scope.spawn(|| checker.check_reader(goals, BufReader::with_capacity(1 << 20, reader)));
        let mut sink = ProofSink(RuleScan {
            inner: BufWriter::with_capacity(1 << 20, writer),
            line: Vec::new(),
            spaces: 0,
            rules: Default::default(),
        });
        let written = write(&mut sink)
            .and_then(|()| sink.flush().map_err(|e| e.to_string()))
            .map(|()| {
                std::mem::take(&mut sink.0.rules)
                    .into_iter()
                    .collect::<Vec<_>>()
            });
        // Closing the pipe ends the kernel's input.
        drop(sink);
        let report = kernel
            .join()
            .unwrap_or_else(|_| Err("kernel panicked".to_string()));
        (report, written)
    });
    // A kernel rejection explains more than the writer's broken pipe.
    let report = report?;
    let rules = written?;
    Ok((report, rules))
}
