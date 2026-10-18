//! A small explicit core source format for fresh certificate generation.
//! This is separate from the ordinary `.hn` surface language for now.
use super::{
    ast::{Face, Interval, Term},
    producer::{self, Generated, Judgment, Request},
};
use crate::sexp::{self, Result, Sexp};

fn shape(s: &Sexp) -> Result<(&str, &[Sexp])> {
    let xs = s.list()?;
    Ok((xs.first().ok_or("empty expression")?.atom()?, &xs[1..]))
}

fn number(s: &Sexp) -> Result<usize> {
    let text = s.atom()?;
    if text.is_empty() || !text.bytes().all(|c| c.is_ascii_digit()) {
        return Err("expected a decimal natural number".into());
    }
    let n = text
        .parse::<usize>()
        .map_err(|_| "natural number is too large")?;
    if n > 32 {
        return Err("source level/index/scope exceeds 32".into());
    }
    Ok(n)
}

/// Entries include anonymous binders: omitting them would capture named
/// references when legacy index syntax and named syntax are mixed.
#[derive(Clone, Default)]
struct Names {
    ordinary: Vec<Option<String>>,
    dimensions: Vec<Option<String>>,
}

fn binder(s: &Sexp) -> Result<String> {
    let name = s.atom()?;
    let mut chars = name.chars();
    if !chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        || !chars.all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '.' | '\''))
    {
        return Err(format!("invalid binder name {name}"));
    }
    if [
        "nat", "zero", "i0", "i1", "u", "v", "dim", "pi", "lam", "app", "path", "plam", "papp",
        "neg", "meet", "join", "scope", "ff", "ft", "at0", "at1", "fand", "for", "system", "comp",
        "sigma", "pair", "fst", "snd",
    ]
    .contains(&name)
    {
        return Err(format!("reserved binder name {name}"));
    }
    Ok(name.to_owned())
}

impl Names {
    fn under(&self, dimension: bool, name: Option<&Sexp>) -> Result<Self> {
        let mut out = self.clone();
        let stack = if dimension {
            &mut out.dimensions
        } else {
            &mut out.ordinary
        };
        stack.push(name.map(binder).transpose()?);
        Ok(out)
    }

    fn lookup(&self, name: &str, dimension: bool) -> Result<usize> {
        let stack = if dimension {
            &self.dimensions
        } else {
            &self.ordinary
        };
        stack
            .iter()
            .rev()
            .position(|n| n.as_deref() == Some(name))
            .ok_or_else(|| {
                format!(
                    "unknown {} name {name}",
                    if dimension { "dimension" } else { "term" }
                )
            })
    }
}

fn interval(s: &Sexp, depth: usize, names: &Names) -> Result<Interval> {
    if depth > 32 {
        return Err("interval nesting exceeds 32".into());
    }
    if let Sexp::Atom(a) = s {
        return Ok(match a.as_str() {
            "i0" => Interval::Zero,
            "i1" => Interval::One,
            _ => Interval::Var(names.lookup(a, true)?),
        });
    }
    let r = |s| interval(s, depth + 1, names).map(Box::new);
    Ok(match shape(s)? {
        ("dim", [n]) => Interval::Var(number(n)?),
        ("neg", [a]) => Interval::Neg(r(a)?),
        ("meet", [a, b]) => Interval::Meet(r(a)?, r(b)?),
        ("join", [a, b]) => Interval::Join(r(a)?, r(b)?),
        _ => return Err(format!("invalid interval expression {s}")),
    })
}

fn face(s: &Sexp, depth: usize, names: &Names) -> Result<Face> {
    if depth > 32 {
        return Err("face nesting exceeds 32".into());
    }
    if let Sexp::Atom(a) = s {
        return match a.as_str() {
            "ff" => Ok(Face::False),
            "ft" => Ok(Face::True),
            _ => Err(format!("unknown face {a}")),
        };
    }
    let f = |s| face(s, depth + 1, names).map(Box::new);
    Ok(match shape(s)? {
        (kind @ ("at0" | "at1"), [n]) => {
            let text = n.atom()?;
            let index = if text.bytes().all(|c| c.is_ascii_digit()) {
                number(n)?
            } else {
                names.lookup(text, true)?
            };
            Face::End(index, kind == "at1")
        }
        ("fand", [a, b]) => Face::And(f(a)?, f(b)?),
        ("for", [a, b]) => Face::Or(f(a)?, f(b)?),
        _ => return Err(format!("invalid face expression {s}")),
    })
}

fn ordinary_binder(
    kind: &str,
    name: Option<&Sexp>,
    a: &Sexp,
    b: &Sexp,
    depth: usize,
    names: &Names,
) -> Result<Term> {
    let domain = Box::new(term(a, depth + 1, names)?);
    let body = Box::new(term(b, depth + 1, &names.under(false, name)?)?);
    Ok(match kind {
        "pi" => Term::Pi(domain, body),
        "sigma" => Term::Sigma(domain, body),
        _ => Term::Lam(domain, body),
    })
}

fn path_binder(
    name: Option<&Sexp>,
    family: &Sexp,
    body: &Sexp,
    depth: usize,
    names: &Names,
) -> Result<Term> {
    let inner = names.under(true, name)?;
    Ok(Term::PathLam(
        Box::new(term(family, depth + 1, &inner)?),
        Box::new(term(body, depth + 1, &inner)?),
    ))
}

fn path_type(
    name: Option<&Sexp>,
    a: &Sexp,
    b: &Sexp,
    c: &Sexp,
    depth: usize,
    names: &Names,
) -> Result<Term> {
    Ok(Term::Path(
        Box::new(term(a, depth + 1, &names.under(true, name)?)?),
        Box::new(term(b, depth + 1, names)?),
        Box::new(term(c, depth + 1, names)?),
    ))
}

fn composition(name: Option<&Sexp>, args: &[Sexp], depth: usize, names: &Names) -> Result<Term> {
    let [family, phi, tube, base] = args else {
        return Err("composition requires FAMILY FACE TUBE BASE".into());
    };
    let inner = names.under(true, name)?;
    Ok(Term::Comp(
        Box::new(term(family, depth + 1, &inner)?),
        face(phi, depth + 1, names)?,
        Box::new(term(tube, depth + 1, &inner)?),
        Box::new(term(base, depth + 1, names)?),
    ))
}

fn term(s: &Sexp, depth: usize, names: &Names) -> Result<Term> {
    if depth > 32 {
        return Err("term nesting exceeds 32".into());
    }
    if let Sexp::Atom(a) = s {
        return Ok(match a.as_str() {
            "nat" => Term::Nat,
            "zero" => Term::Zero,
            _ => Term::Var(names.lookup(a, false)?),
        });
    }
    let t = |s| term(s, depth + 1, names).map(Box::new);
    Ok(match shape(s)? {
        ("u", [n]) => Term::Universe(number(n)?),
        ("v", [n]) => Term::Var(number(n)?),
        (kind @ ("pi" | "lam" | "sigma"), [a, b]) => {
            ordinary_binder(kind, None, a, b, depth, names)?
        }
        (kind @ ("pi" | "lam" | "sigma"), [name, a, b]) => {
            ordinary_binder(kind, Some(name), a, b, depth, names)?
        }
        ("app", [f, a]) => Term::App(t(f)?, t(a)?),
        ("pair", [ty, a, b]) => Term::Pair(t(ty)?, t(a)?, t(b)?),
        ("fst", [p]) => Term::Fst(t(p)?),
        ("snd", [p]) => Term::Snd(t(p)?),
        ("path", [a, b, c]) => path_type(None, a, b, c, depth, names)?,
        ("path", [name, a, b, c]) => path_type(Some(name), a, b, c, depth, names)?,
        ("plam", [a, b]) => path_binder(None, a, b, depth, names)?,
        ("plam", [name, a, b]) => path_binder(Some(name), a, b, depth, names)?,
        ("papp", [p, r]) => Term::PathApp(t(p)?, interval(r, depth + 1, names)?),
        ("comp", args @ [_, _, _, _]) => composition(None, args, depth, names)?,
        ("comp", [name, rest @ ..]) => composition(Some(name), rest, depth, names)?,
        ("system", [ty, sides]) => {
            let sides = sides.list()?;
            if sides.len() > 16 {
                return Err("system exceeds 16 branches".into());
            }
            let mut branches = Vec::new();
            for side in sides {
                let [phi, value] = side.list()? else {
                    return Err("system branch requires (FACE TERM)".into());
                };
                branches.push((face(phi, depth + 1, names)?, term(value, depth + 1, names)?));
            }
            Term::System(t(ty)?, branches)
        }
        _ => return Err(format!("invalid term expression {s}")),
    })
}

fn scope(s: &Sexp) -> Result<(Names, Vec<Term>)> {
    let ("scope", [dimensions, context]) = shape(s)? else {
        return Err("expected (scope DIMENSIONS CONTEXT)".into());
    };
    let mut names = Names::default();
    let named = matches!(dimensions, Sexp::List(_));
    if named {
        let dims = dimensions.list()?;
        if dims.len() > 32 {
            return Err("source dimension scope exceeds 32".into());
        }
        let mut seen = std::collections::BTreeSet::new();
        for dim in dims {
            let name = binder(dim)?;
            if !seen.insert(name.clone()) {
                return Err(format!("duplicate dimension name {name}"));
            }
            names.dimensions.push(Some(name));
        }
    } else {
        names.dimensions = vec![None; number(dimensions)?];
    }
    let entries = context.list()?;
    if entries.len() > 32 {
        return Err("source context exceeds 32 entries".into());
    }
    let mut types = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for entry in entries {
        let (name, ty) = if named {
            let [name, ty] = entry.list()? else {
                return Err("named context requires (NAME TYPE) entries".into());
            };
            let name = binder(name)?;
            if !seen.insert(name.clone()) {
                return Err(format!("duplicate context name {name}"));
            }
            (Some(name), ty)
        } else {
            (None, entry)
        };
        // A name is not in scope in its own domain, nor in earlier entries.
        types.push(term(ty, 0, &names)?);
        names.ordinary.push(name);
    }
    Ok((names, types))
}

/// Read explicit assertions. There are no theory/rule/axiom declarations or
/// implicit imports; a source file cannot enlarge the selected theory.
pub fn parse(src: &str) -> Result<Vec<Request>> {
    if src.len() > 1 << 20 {
        return Err("cubical source exceeds 1 MiB".into());
    }
    let forms = sexp::parse(src)?;
    if forms.is_empty() || forms.len() > 128 {
        return Err("expected 1..128 cubical assertions".into());
    }
    forms
        .iter()
        .enumerate()
        .map(|(i, form)| {
            let assertion = || -> Result<Request> {
                let (kind, fields) = shape(form)?;
                let (name, mut fields) = fields.split_first().ok_or("assertion requires a name")?;
                let name = name.atom()?.to_owned();
                let (mut names, mut context) = (Names::default(), Vec::new());
                if let Some(Sexp::List(spec)) = fields.first()
                    && spec.first().is_some_and(|s| s == &sexp::atom("scope"))
                {
                    (names, context) = scope(&fields[0])?;
                    fields = &fields[1..];
                }
                let dimensions = names.dimensions.len();
                let judgment = match (kind, fields) {
                    ("check", [t, ty]) => Judgment::Has {
                        term: term(t, 0, &names)?,
                        ty: term(ty, 0, &names)?,
                    },
                    ("equal", [left, right, ty]) => Judgment::Equal {
                        left: term(left, 0, &names)?,
                        right: term(right, 0, &names)?,
                        ty: term(ty, 0, &names)?,
                    },
                    ("entails", [a, b]) => Judgment::Entails {
                        premise: face(a, 0, &names)?,
                        conclusion: face(b, 0, &names)?,
                    },
                    ("local", [phi, r, s]) => Judgment::Local {
                        face: face(phi, 0, &names)?,
                        left: interval(r, 0, &names)?,
                        right: interval(s, 0, &names)?,
                    },
                    ("check-on", [phi,t,ty]) => Judgment::RestrictedHas { face: face(phi,0,&names)?, term: term(t,0,&names)?, ty: term(ty,0,&names)? },
                    ("equal-on", [phi,a,b,ty]) => Judgment::RestrictedEqual { face: face(phi,0,&names)?, left: term(a,0,&names)?, right: term(b,0,&names)?, ty: term(ty,0,&names)? },
                    _ => {
                        return Err(
                            "expected check/equal/entails/local/check-on/equal-on assertion with optional scope"
                                .into(),
                        );
                    }
                };
                Ok(Request {
                    name,
                    dimensions,
                    context,
                    judgment,
                })
            };
            assertion().map_err(|e| format!("assertion {}: {e}", i + 1))
        })
        .collect()
}

/// Parse a source file, generate fresh evidence and check its fixed goals.
pub fn run(src: &str) -> Result<Generated> {
    producer::produce(&parse(src)?)
}
