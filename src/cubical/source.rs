//! A small explicit core source format for fresh certificate generation.
//! This is separate from the ordinary `.hn` surface language for now.
use super::{
    ast::{Interval, Term},
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

fn interval(s: &Sexp, depth: usize) -> Result<Interval> {
    if depth > 32 {
        return Err("interval nesting exceeds 32".into());
    }
    if let Sexp::Atom(a) = s {
        return match a.as_str() {
            "i0" => Ok(Interval::Zero),
            "i1" => Ok(Interval::One),
            _ => Err(format!("unknown interval {a}")),
        };
    }
    Ok(match shape(s)? {
        ("dim", [n]) => Interval::Var(number(n)?),
        ("neg", [r]) => Interval::Neg(Box::new(interval(r, depth + 1)?)),
        ("meet", [r, t]) => Interval::Meet(
            Box::new(interval(r, depth + 1)?),
            Box::new(interval(t, depth + 1)?),
        ),
        ("join", [r, t]) => Interval::Join(
            Box::new(interval(r, depth + 1)?),
            Box::new(interval(t, depth + 1)?),
        ),
        _ => return Err(format!("invalid interval expression {s}")),
    })
}

fn term(s: &Sexp, depth: usize) -> Result<Term> {
    if depth > 32 {
        return Err("term nesting exceeds 32".into());
    }
    if let Sexp::Atom(a) = s {
        return match a.as_str() {
            "nat" => Ok(Term::Nat),
            "zero" => Ok(Term::Zero),
            _ => Err(format!("unknown term {a}")),
        };
    }
    let t = |s| term(s, depth + 1).map(Box::new);
    Ok(match shape(s)? {
        ("u", [n]) => Term::Universe(number(n)?),
        ("v", [n]) => Term::Var(number(n)?),
        ("pi", [a, b]) => Term::Pi(t(a)?, t(b)?),
        ("lam", [a, b]) => Term::Lam(t(a)?, t(b)?),
        ("app", [f, a]) => Term::App(t(f)?, t(a)?),
        ("path", [a, b, c]) => Term::Path(t(a)?, t(b)?, t(c)?),
        ("plam", [a, b]) => Term::PathLam(t(a)?, t(b)?),
        ("papp", [p, r]) => Term::PathApp(t(p)?, interval(r, depth + 1)?),
        _ => return Err(format!("invalid term expression {s}")),
    })
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
    forms.iter().enumerate().map(|(i, form)| {
        let assertion = || -> Result<Request> {
            let (kind, fields) = shape(form)?;
            let (name, mut fields) = fields.split_first().ok_or("assertion requires a name")?;
            let name = name.atom()?.to_owned();
            let (mut dimensions, mut context) = (0, Vec::new());
            if let Some(Sexp::List(scope)) = fields.first()
                && scope.first().is_some_and(|s| s == &sexp::atom("scope")) {
                let (_, [d, g]) = shape(&fields[0])? else { return Err("expected (scope DIMENSIONS (CONTEXT-TYPES...))".into()); };
                dimensions = number(d)?;
                let types = g.list()?;
                if types.len() > 32 { return Err("source context exceeds 32 entries".into()); }
                context = types.iter().map(|a| term(a, 0)).collect::<Result<_>>()?;
                fields = &fields[1..];
            }
            let judgment = match (kind, fields) {
                ("check", [t, ty]) => Judgment::Has { term: term(t, 0)?, ty: term(ty, 0)? },
                ("equal", [left, right, ty]) => Judgment::Equal { left: term(left, 0)?, right: term(right, 0)?, ty: term(ty, 0)? },
                _ => return Err("expected (check NAME [SCOPE] TERM TYPE) or (equal NAME [SCOPE] LEFT RIGHT TYPE)".into()),
            };
            Ok(Request { name, dimensions, context, judgment })
        };
        assertion().map_err(|e| format!("assertion {}: {e}", i + 1))
    }).collect()
}

/// Parse a source file, generate fresh evidence and check its fixed goals.
pub fn run(src: &str) -> Result<Generated> {
    producer::produce(&parse(src)?)
}
