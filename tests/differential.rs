//! Differential tests against the extraction-time kernel. Compact forms are
//! first expanded by an independent tree-based reference into ordinary
//! certificates, which the legacy kernel then checks. The new kernel must
//! accept exactly when that pipeline accepts.
#[path = "support/legacy_kernel.rs"]
#[allow(dead_code)]
mod legacy;
use horn::{compress::compress, kernel::Theory, sexp::Sexp, sexp::parse};
use std::collections::HashMap;

const THEORY: &str = "(sort A) (sort B)
    (ctor z () A) (ctor s (A) A) (ctor pair (A A) B) (ctor q () B)
    (pred le (A A)) (pred ok (B)) (pred s (A)) (pred top ())
    (rule le.z () (le z ?n))
    (rule le.s ((le ?m ?n)) (le (s ?m) (s ?n)))
    (rule mk ((le ?a ?b)) (ok (pair ?a ?b)))
    (rule pick ((ok (pair ?a ?b)) (ok (pair ?b ?c))) (ok (pair ?a ?c)))
    (rule refl ((le ?a ?a)) (s ?a))
    (rule top () (top))
    (rule from-top ((top)) (ok q))";

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

fn atom(s: &str) -> Sexp {
    Sexp::Atom(s.into())
}
fn list(xs: Vec<Sexp>) -> Sexp {
    Sexp::List(xs)
}

struct Reference {
    rules: HashMap<String, (Vec<Sexp>, Sexp)>,
    ctors: HashMap<String, (Vec<String>, String)>,
}

impl Reference {
    fn new(theory: &str) -> Self {
        let mut r = Self {
            rules: HashMap::new(),
            ctors: HashMap::new(),
        };
        for form in parse(theory).unwrap() {
            let xs = form.list().unwrap();
            let name = xs[1].atom().unwrap().to_owned();
            match xs[0].atom().unwrap() {
                "rule" => {
                    r.rules
                        .insert(name, (xs[2].list().unwrap().to_vec(), xs[3].clone()));
                }
                "ctor" => {
                    let inputs = xs[2].list().unwrap().iter().map(|s| s.to_string());
                    r.ctors.insert(name, (inputs.collect(), xs[3].to_string()));
                }
                _ => {}
            }
        }
        r
    }

    fn sort(&self, t: &Sexp) -> Option<String> {
        let (head, args) = match t {
            Sexp::Atom(a) => (a.as_str(), &[][..]),
            Sexp::List(xs) if xs.len() > 1 => (xs[0].atom().ok()?, &xs[1..]),
            _ => return None,
        };
        let (inputs, output) = self.ctors.get(head)?;
        let ok = inputs.len() == args.len()
            && args
                .iter()
                .zip(inputs)
                .all(|(a, s)| self.sort(a).as_ref() == Some(s));
        ok.then(|| output.clone())
    }

    /// Replace abbreviations; `None` for an undefined one.
    fn expand(t: &Sexp, defs: &HashMap<String, Sexp>) -> Option<Sexp> {
        match t {
            Sexp::Atom(a) if a.starts_with('?') => defs.get(a).cloned(),
            Sexp::Atom(_) => Some(t.clone()),
            Sexp::List(xs) => xs
                .iter()
                .map(|x| Self::expand(x, defs))
                .collect::<Option<_>>()
                .map(list),
        }
    }

    fn unify(p: &Sexp, g: &Sexp, b: &mut HashMap<String, Sexp>) -> bool {
        match (p, g) {
            (Sexp::Atom(v), _) if v.starts_with('?') => {
                b.entry(v.clone()).or_insert(g.clone()) == g
            }
            (Sexp::Atom(x), Sexp::Atom(y)) => x == y,
            (Sexp::List(ps), Sexp::List(gs)) => {
                ps.len() == gs.len() && ps.iter().zip(gs).all(|(p, g)| Self::unify(p, g, b))
            }
            _ => false,
        }
    }

    fn instantiate(p: &Sexp, b: &HashMap<String, Sexp>) -> Option<Sexp> {
        match p {
            Sexp::Atom(v) if v.starts_with('?') => b.get(v).cloned(),
            Sexp::Atom(_) => Some(p.clone()),
            Sexp::List(xs) => xs
                .iter()
                .map(|x| Self::instantiate(x, b))
                .collect::<Option<_>>()
                .map(list),
        }
    }

    /// Expand a certificate that may use compact forms into ordinary forms.
    fn ordinary(&self, proof: &str) -> Option<String> {
        let mut defs = HashMap::new();
        let mut facts: Vec<Sexp> = Vec::new();
        let mut out = String::new();
        for form in parse(proof).ok()? {
            let xs = form.list().ok()?;
            match xs.first()?.atom().ok()? {
                "def" if xs.len() == 3 => {
                    let name = xs[1].atom().ok()?;
                    let term = Self::expand(&xs[2], &defs)?;
                    if !name.starts_with('?') || name.len() == 1 || defs.contains_key(name) {
                        return None;
                    }
                    self.sort(&term)?;
                    defs.insert(name.to_owned(), term);
                }
                "step" if xs.len() >= 4 => {
                    let (premises, conclusion) = self.rules.get(xs[2].atom().ok()?)?;
                    let refs = xs[3].list().ok()?;
                    let mut b = HashMap::new();
                    let mut stated = None;
                    for item in &xs[4..] {
                        let ys = item.list().ok()?;
                        let head = ys.first()?.atom().ok()?;
                        if head.starts_with('?') {
                            let value = Self::expand(ys.get(1)?, &defs)?;
                            let known = premises
                                .iter()
                                .chain([conclusion])
                                .any(|p| p.to_string().split([' ', '(', ')']).any(|w| w == head));
                            if ys.len() != 2 || !known || b.insert(head.to_owned(), value).is_some()
                            {
                                return None;
                            }
                        } else if stated.replace(Self::expand(item, &defs)?).is_some() {
                            return None;
                        }
                    }
                    if let Some(j) = &stated
                        && !Self::unify(conclusion, j, &mut b)
                    {
                        return None;
                    }
                    if refs.len() == premises.len() {
                        for (p, r) in premises.iter().zip(refs) {
                            let fact = facts.get(r.atom().ok()?.parse::<usize>().ok()?)?;
                            if !Self::unify(p, fact, &mut b) {
                                return None;
                            }
                        }
                    }
                    let j = match stated {
                        Some(j) => j,
                        None => Self::instantiate(conclusion, &b)?,
                    };
                    out += &format!("(step {} {} {} {j})\n", xs[1], xs[2], xs[3]);
                    facts.push(j);
                }
                "step" => return None,
                _ => out += &format!("{form}\n"),
            }
        }
        Some(out)
    }
}

fn small(rng: &mut Rng) -> Sexp {
    let mut t = atom("z");
    for _ in 0..rng.below(3) {
        t = list(vec![atom("s"), t]);
    }
    t
}

/// A random, mostly valid certificate in a random mix of styles.
fn certificate(rng: &mut Rng, r: &Reference) -> (String, String) {
    let names = ["le.z", "le.s", "mk", "pick", "refl", "top", "from-top"];
    let mut facts: Vec<Sexp> = Vec::new();
    let mut proof = String::new();
    let mut defs = 0;
    for _ in 0..rng.below(12) + 1 {
        let name = names[rng.below(names.len())];
        let (premises, conclusion) = &r.rules[name];
        let mut b = HashMap::new();
        let mut refs = Vec::new();
        for p in premises {
            let found = (0..8).map(|_| rng.below(facts.len().max(1))).find(|&i| {
                facts
                    .get(i)
                    .is_some_and(|f| Reference::unify(p, f, &mut b.clone()))
            });
            let Some(i) = found else { break };
            Reference::unify(p, &facts[i], &mut b);
            refs.push(i);
        }
        if refs.len() != premises.len() {
            continue;
        }
        for v in ["?n", "?a", "?b", "?c", "?m"] {
            b.entry(v.to_owned()).or_insert_with(|| small(rng));
        }
        let j = Reference::instantiate(conclusion, &b).unwrap();
        let refs = refs
            .iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join(" ");
        let i = facts.len();
        match rng.below(4) {
            0 | 1 => proof += &format!("(step {i} {name} ({refs}) {j})\n"),
            style => {
                let mut items = String::new();
                for v in ["?n", "?a", "?b", "?c", "?m"] {
                    let in_conclusion = conclusion.to_string().contains(v);
                    let in_premise = premises.iter().any(|p| p.to_string().contains(v));
                    if in_conclusion && (!in_premise || rng.below(4) == 0) {
                        let mut value = b[v].to_string();
                        if style == 3 {
                            proof += &format!("(def ?d{defs} {value})\n");
                            value = format!("?d{defs}");
                            defs += 1;
                        }
                        items += &format!(" ({v} {value})");
                    }
                }
                if rng.below(5) == 0 {
                    items += &format!(" {j}");
                }
                proof += &format!("(step {i} {name} ({refs}){items})\n");
            }
        }
        facts.push(j);
    }
    let mut goals = String::new();
    for k in 0..rng.below(3) + 1 {
        if facts.is_empty() {
            break;
        }
        let i = rng.below(facts.len());
        goals += &format!("(goal g{k} {})\n", facts[i]);
        proof += &format!("(result g{k} {i})\n");
    }
    (goals, proof)
}

fn mutate(rng: &mut Rng, text: &str) -> String {
    let vocab = [
        "(",
        ")",
        "z",
        "s",
        "q",
        "?n",
        "?a",
        "?d0",
        "?",
        "0",
        "1",
        "+1",
        "le",
        "ok",
        "top",
        "step",
        "def",
        "result",
        "le.z",
        "mk",
        "(s z)",
        "(pair z z)",
        "(top)",
    ];
    let mut tokens: Vec<String> = text
        .replace('(', " ( ")
        .replace(')', " ) ")
        .split_whitespace()
        .map(str::to_owned)
        .collect();
    for _ in 0..rng.below(3) + 1 {
        if tokens.is_empty() {
            break;
        }
        let i = rng.below(tokens.len());
        match rng.below(4) {
            0 => {
                tokens.remove(i);
            }
            1 => tokens.insert(i, vocab[rng.below(vocab.len())].into()),
            2 => tokens[i] = vocab[rng.below(vocab.len())].into(),
            _ => {
                let j = rng.below(tokens.len());
                tokens.swap(i, j);
            }
        }
    }
    tokens.join(" ")
}

#[test]
fn kernel_agrees_with_legacy_kernel_on_random_certificates() {
    let reference = Reference::new(THEORY);
    let theory = Theory::parse(THEORY).unwrap();
    let old = legacy::Theory::parse(THEORY).unwrap();
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let (mut accepted, mut compact_accepted) = (0, 0);
    for case in 0..60_000 {
        let (mut goals, mut proof) = certificate(&mut rng, &reference);
        if case % 2 == 1 {
            proof = mutate(&mut rng, &proof);
        }
        if case % 13 == 0 {
            goals = mutate(&mut rng, &goals);
        }
        let new = theory.check(&goals, &proof).is_ok();
        let expected = reference
            .ordinary(&proof)
            .is_some_and(|ordinary| old.check(&goals, &ordinary).is_ok());
        assert_eq!(new, expected, "goals:\n{goals}\nproof:\n{proof}");
        // Ordinary certificates keep exactly their former verdict.
        if !proof.contains("def")
            && parse(&proof).is_ok_and(|forms| {
                forms.iter().all(|f| {
                    f.list().is_ok_and(|xs| {
                        xs.first().and_then(|h| h.atom().ok()) != Some("step")
                            || (xs.len() == 5 && !xs[4].to_string().starts_with("(?"))
                    })
                })
            })
        {
            assert_eq!(new, old.check(&goals, &proof).is_ok(), "proof:\n{proof}");
            if new && let Some(ordinary) = reference.ordinary(&proof) {
                let mut out = Vec::new();
                compress(THEORY, ordinary.as_bytes(), &mut out).unwrap();
                let out = String::from_utf8(out).unwrap();
                assert!(
                    theory.check(&goals, &out).is_ok(),
                    "{proof}\ncompressed:\n{out}"
                );
                compact_accepted += 1;
            }
        }
        accepted += usize::from(new);
    }
    assert!(
        accepted > 20_000 && compact_accepted > 4_000,
        "{accepted} {compact_accepted}"
    );
}

#[test]
fn compact_forms_are_checked_like_stated_conclusions() {
    let theory = Theory::parse(THEORY).unwrap();
    let ok = |goals: &str, proof: &str| theory.check(goals, proof).is_ok();
    let goal = "(goal g (ok (pair (s z) (s (s z)))))";
    let base = "(step 0 le.z () (?n (s z))) (step 1 le.s (0)) (step 2 mk (1))";
    assert!(ok(goal, &format!("{base} (result g 2)")));
    let shared = base.replace("(s z))", "?x)");
    assert!(ok(goal, &format!("(def ?x (s z)) {shared} (result g 2)")));
    for bad in [
        "(step 0 le.z ()) (result g 0)",                     // unbound ?n
        "(step 0 le.z () (?n q)) (result g 0)",              // ill-sorted binding
        "(step 0 le.z () (?x z)) (result g 0)",              // not a rule variable
        "(step 0 le.z () (?n z) (?n z)) (result g 0)",       // repeated binding
        "(step 0 le.z () (?n z) (le z (s z))) (result g 0)", // binding contradicts conclusion
        "(step 0 le.z () (le z z) (le z z)) (result g 0)",   // two conclusions
        "(def ?x q) (step 0 le.z () (?n ?x)) (result g 0)",  // ill-sorted abbreviation
        "(def ?x z) (def ?x z) (step 0 le.z () (?n ?x)) (result g 0)",
        "(def x z) (step 0 le.z () (?n z)) (result g 0)",
        "(def ?x (le z z)) (step 0 le.z () (?n z)) (result g 0)",
        "(step 0 le.z () (?n ?y)) (result g 0)",
    ] {
        assert!(!ok("(goal g (le z z))", bad), "accepted {bad}");
    }
    assert!(ok(
        "(goal g (le z z))",
        "(step 0 le.z () (?n z) (le z z)) (result g 0)"
    ));
    // Abbreviations are proof-local: goals cannot use them.
    assert!(!ok(
        "(goal g (le z ?x))",
        "(def ?x z) (step 0 le.z () (?n z)) (result g 0)"
    ));
}

#[test]
fn theory_declarations_agree_with_legacy_kernel() {
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    let reference = Reference::new(THEORY);
    let mut both = 0;
    for _ in 0..80_000 {
        let theory = mutate(&mut rng, THEORY);
        let (new, old) = (Theory::parse(&theory), legacy::Theory::parse(&theory));
        assert_eq!(new.is_ok(), old.is_ok(), "theory:\n{theory}");
        if let (Ok(new), Ok(old)) = (new, old) {
            let (goals, proof) = certificate(&mut rng, &reference);
            let ordinary = reference.ordinary(&proof).unwrap_or_default();
            assert_eq!(
                new.check(&goals, &ordinary).is_ok(),
                old.check(&goals, &ordinary).is_ok(),
                "theory:\n{theory}\nproof:\n{ordinary}"
            );
            both += 1;
        }
    }
    assert!(both > 1_000, "{both}");
}
