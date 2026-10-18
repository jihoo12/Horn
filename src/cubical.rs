//! Explicit cubical data and untrusted certificate generation. No new
//! inference or reduction algorithm in the kernel. See docs/CUBICAL.md.

pub mod ast;
pub mod engine;
pub mod generate;
pub mod script;
pub mod producer;
pub mod source;

/// Order matters: later fragments use declarations from earlier fragments.
pub const FRAGMENTS: &[(&str, &str)] = &[
    ("path", include_str!("../theories/cubical/path.horn")),
    ("faces", include_str!("../theories/cubical/faces.horn")),
    (
        "face-ops",
        include_str!("../theories/cubical/face-ops.horn"),
    ),
    (
        "restricted",
        include_str!("../theories/cubical/restricted.horn"),
    ),
    ("systems", include_str!("../theories/cubical/systems.horn")),
    (
        "composition",
        include_str!("../theories/cubical/composition.horn"),
    ),
    ("sigma", include_str!("../theories/cubical/sigma.horn")),
    (
        "equivalence-defs",
        include_str!("../theories/cubical/equivalence-defs.horn"),
    ),
    ("glue", include_str!("../theories/cubical/glue.horn")),
    (
        "equality",
        include_str!("../theories/cubical/equality.horn"),
    ),
    (
        "canonical-map",
        include_str!("../theories/cubical/canonical-map.horn"),
    ),
    (
        "computation",
        include_str!("../theories/cubical/computation.horn"),
    ),
    // Appended after the kamo3 snapshot; oracles encoded against the
    // twelve fragments above decode unchanged (oracle format 2).
    ("bool", include_str!("../theories/cubical/bool.horn")),
    ("nat", include_str!("../theories/cubical/nat.horn")),
    ("circle", include_str!("../theories/cubical/circle.horn")),
];

/// Predicates of the snapshot's unrestricted judgment layer. The restricted
/// layer (`rctx`, `rhas`, `req`) states the same judgments under a face, and
/// scripts use only it.
pub const UNRESTRICTED: &[&str] = &["ctx", "has", "eq"];

/// The theory for scripts: the bundled theory without the unrestricted
/// layer, i.e. without the declarations of its predicates and every rule
/// whose conclusion or premises use one of them (its typing and equality
/// rules and the bridges `rhas.global`, `rhas.export`, ...). Nothing else is
/// changed; the remaining rules never mention those predicates.
pub fn core_theory() -> String {
    let uses = |form: &crate::sexp::Sexp| -> bool {
        let Ok(xs) = form.list() else { return false };
        let head = xs.first().and_then(|h| h.atom().ok());
        match head {
            Some("pred") => xs.get(1).and_then(|n| n.atom().ok()).is_some_and(|n| UNRESTRICTED.contains(&n)),
            Some("rule") if xs.len() == 4 => {
                let pred = |j: &crate::sexp::Sexp| {
                    j.list().ok().and_then(|ys| ys.first()?.atom().ok()).is_some_and(|p| UNRESTRICTED.contains(&p))
                };
                pred(&xs[3]) || xs[2].list().is_ok_and(|ps| ps.iter().any(pred))
            }
            _ => false,
        }
    };
    let mut kept = Vec::new();
    for (name, source) in FRAGMENTS {
        for form in crate::sexp::parse(source).expect("bundled theory parses") {
            if !uses(&form) {
                kept.push((*name, form));
            }
        }
    }
    // A rule that is an instance of another rule, with its premises among
    // the instance's, derives nothing new; drop it (req.comp-nat-zero).
    let rules: Vec<&crate::sexp::Sexp> = kept.iter().map(|(_, f)| f).filter(|f| is_rule(f)).collect();
    let redundant: Vec<bool> = kept
        .iter()
        .map(|(_, f)| is_rule(f) && rules.iter().any(|g| !std::ptr::eq(*g, f) && covers(g, f) && !covers(f, g)))
        .collect();
    let mut out = String::new();
    let mut last = "";
    for ((name, form), drop) in kept.iter().zip(redundant) {
        if *name != last {
            out.push_str(&format!("; {name} (core)\n"));
            last = name;
        }
        if !drop {
            out.push_str(&format!("{form}\n"));
        }
    }
    out
}

fn is_rule(f: &crate::sexp::Sexp) -> bool {
    f.list().is_ok_and(|xs| xs.len() == 4 && xs[0].atom().ok() == Some("rule"))
}

/// One-way matching of a rule pattern against a term whose `?` variables
/// are treated as constants.
fn matches(
    p: &crate::sexp::Sexp,
    t: &crate::sexp::Sexp,
    sub: &mut Vec<(String, crate::sexp::Sexp)>,
) -> bool {
    use crate::sexp::Sexp;
    match (p, t) {
        (Sexp::Atom(v), _) if v.starts_with('?') => match sub.iter().find(|(n, _)| n == v) {
            Some((_, bound)) => bound == t,
            None => {
                sub.push((v.clone(), t.clone()));
                true
            }
        },
        (Sexp::Atom(a), Sexp::Atom(b)) => a == b,
        (Sexp::List(xs), Sexp::List(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| matches(x, y, sub))
        }
        _ => false,
    }
}

/// Whether rule `general` derives rule `special` in one step: its
/// conclusion matches, and each of its premises matches one of `special`'s.
fn covers(general: &crate::sexp::Sexp, special: &crate::sexp::Sexp) -> bool {
    let (g, s) = (general.list().unwrap(), special.list().unwrap());
    let mut sub = Vec::new();
    if !matches(&g[3], &s[3], &mut sub) {
        return false;
    }
    fn go(
        premises: &[crate::sexp::Sexp],
        available: &[crate::sexp::Sexp],
        sub: &[(String, crate::sexp::Sexp)],
    ) -> bool {
        let Some((first, rest)) = premises.split_first() else {
            return true;
        };
        available.iter().any(|q| {
            let mut s = sub.to_vec();
            matches(first, q, &mut s) && go(rest, available, &s)
        })
    }
    go(g[2].list().unwrap_or(&[]), s[2].list().unwrap_or(&[]), &sub)
}

pub fn theory() -> String {
    FRAGMENTS
        .iter()
        .map(|(_, source)| format!("{source}\n"))
        .collect()
}

pub struct Example {
    pub name: &'static str,
    pub description: &'static str,
    pub goals: &'static str,
    pub oracle: &'static [u8],
}

pub const EXAMPLES: &[Example] = &[
    Example {
        name: "univalence",
        description: "U0 univalence and its canonical-map function component",
        goals: include_str!("../examples/cubical/deep-univalence.goals"),
        oracle: include_bytes!("../examples/cubical/deep-univalence.oracle"),
    },
    Example {
        name: "ua-transport",
        description: "judgmental transport along ua via Glue composition",
        goals: include_str!("../examples/cubical/ua-transport.goals"),
        oracle: include_bytes!("../examples/cubical/ua-transport.oracle"),
    },
    Example {
        name: "canonicity",
        description: "transport along ua of not on bool computes to a boolean",
        goals: include_str!("../examples/cubical/canonicity.goals"),
        oracle: include_bytes!("../examples/cubical/canonicity.oracle"),
    },
];
