//! Untrusted, bounded execution of function clauses. Each reduction produces
//! an ordinary rule application; the existing certificate checker decides
//! whether that evidence is valid.
use super::{Just, Pat, Proof, Result, Sig, T, Term};

const MAX_DEPTH: usize = 128;
const MAX_CALLS: usize = 10_000;

pub(super) fn is_forward_call(sig: &Sig, term: &Term) -> bool {
    fn ground(t: &Term) -> bool {
        match t {
            Term::Meta(_) => false,
            Term::App(_, args) => args.iter().all(ground),
            _ => true,
        }
    }
    let (name, args): (&str, &[Term]) = match term {
        Term::Name(n) => (n, &[]),
        Term::App(n, args) => (n, args),
        _ => return false,
    };
    sig.defs.contains(name)
        && args.len() + 1 == sig.inputs[sig.sym_ix[name] as usize].len()
        && ground(term)
}

pub(super) fn source_expression(t: &Term) -> String {
    match t {
        Term::Name(n) => n.clone(),
        Term::Meta(n) => format!("?{n}"),
        Term::Num(n) => n.to_string(),
        Term::App(n, args) => format!(
            "{n} {}",
            args.iter()
                .map(|a| match a {
                    Term::App(_, _) => format!("({})", source_expression(a)),
                    a => source_expression(a),
                })
                .collect::<Vec<_>>()
                .join(" ")
        ),
    }
}

pub(super) struct Evaluator<'a> {
    sig: &'a Sig,
    calls: usize,
}

impl<'a> Evaluator<'a> {
    pub(super) fn new(sig: &'a Sig) -> Self {
        Self { sig, calls: 0 }
    }

    fn depth(&self, depth: usize) -> Result<()> {
        if depth > MAX_DEPTH {
            Err("evaluation depth limit exceeded (128); termination is not established".into())
        } else {
            Ok(())
        }
    }

    pub(super) fn expression(&mut self, t: &Term, depth: usize) -> Result<(T, Vec<Proof>)> {
        self.depth(depth)?;
        if let Term::Num(n) = t {
            return self.expression(&self.sig.numeral(*n)?, depth);
        }
        let (name, args): (&str, &[Term]) = match t {
            Term::Name(n) => (n, &[]),
            Term::App(n, args) => (n, args),
            _ => return Err("evaluation requires a ground expression".into()),
        };
        let symbol = *self
            .sig
            .sym_ix
            .get(name)
            .ok_or_else(|| format!("unknown symbol {name}"))?;
        let is_function = self.sig.defs.contains(name);
        if !is_function && self.sig.output[symbol as usize].is_none() {
            return Err(format!("predicate {name} is not an expression"));
        }
        let inputs = &self.sig.inputs[symbol as usize];
        let arity = inputs.len() - usize::from(is_function);
        if args.len() != arity {
            return Err(format!("{name} takes {arity} arguments"));
        }
        let mut values = Vec::new();
        let mut proofs = Vec::new();
        for (arg, &sort) in args.iter().zip(inputs) {
            let (value, mut evidence) = self.expression(arg, depth + 1)?;
            let T::A(c, _) = &value else {
                unreachable!("ground value")
            };
            if self.sig.output[*c as usize] != Some(sort) {
                return Err(format!("argument of {name} has the wrong sort"));
            }
            values.push(value);
            proofs.append(&mut evidence);
        }
        if is_function {
            let (value, proof) = self.call(symbol, &values, depth + 1)?;
            proofs.push(proof);
            Ok((value, proofs))
        } else {
            Ok((T::A(symbol, values.into()), proofs))
        }
    }

    fn call(&mut self, f: u32, inputs: &[T], depth: usize) -> Result<(T, Proof)> {
        self.depth(depth)?;
        self.calls += 1;
        if self.calls > MAX_CALLS {
            return Err(
                "evaluation call limit exceeded (10000); termination is not established".into(),
            );
        }
        let name = &self.sig.names[f as usize];
        for &index in self.sig.clauses.get(&f).into_iter().flatten() {
            let rule = &self.sig.rules[index];
            let Pat::A(_, pats) = &rule.conclusion else {
                unreachable!("function rule")
            };
            let mut env = vec![None; rule.sorts.len()];
            if !pats[..inputs.len()]
                .iter()
                .zip(inputs)
                .all(|(p, t)| bind(p, t, &mut env))
            {
                continue;
            }
            // The first matching clause commits. A partial or diverging body
            // must not fall through to another clause or to proof search.
            let mut children = Vec::new();
            for premise in &rule.premises {
                let Pat::A(g, ps) = premise else {
                    unreachable!("function premise")
                };
                let args = ps[..ps.len() - 1]
                    .iter()
                    .map(|p| instantiate(p, &env))
                    .collect::<Result<Vec<_>>>()?;
                let (value, proof) = self.call(*g, &args, depth + 1)?;
                if !bind(ps.last().unwrap(), &value, &mut env) {
                    return Err(format!("inconsistent result while evaluating {name}"));
                }
                children.push(proof);
            }
            let goal = instantiate(&rule.conclusion, &env)?;
            let T::A(_, args) = &goal else {
                unreachable!("function judgment")
            };
            let value = args.last().unwrap().clone();
            return Ok((
                value,
                Proof {
                    just: Just::Rule(index),
                    goal,
                    children,
                },
            ));
        }
        Err(format!("no matching clause for {name}"))
    }
}

fn bind(p: &Pat, t: &T, env: &mut [Option<T>]) -> bool {
    match (p, t) {
        (Pat::Var(v), t) => match &env[*v] {
            Some(old) => old == t,
            None => {
                env[*v] = Some(t.clone());
                true
            }
        },
        (Pat::A(f, ps), T::A(g, ts)) => {
            f == g && ps.len() == ts.len() && ps.iter().zip(ts.iter()).all(|(p, t)| bind(p, t, env))
        }
        _ => false,
    }
}

fn instantiate(p: &Pat, env: &[Option<T>]) -> Result<T> {
    match p {
        Pat::Var(v) => env[*v]
            .clone()
            .ok_or_else(|| "function result depends on an unbound variable".into()),
        Pat::A(f, ps) => Ok(T::A(
            *f,
            ps.iter()
                .map(|p| instantiate(p, env))
                .collect::<Result<Vec<_>>>()?
                .into(),
        )),
        Pat::E(_) => Err("eigenvariable in a function clause".into()),
    }
}
