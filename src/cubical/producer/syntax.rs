//! Bounds shared by input validation and certified definition lowering.
use super::{Face, Interval, Result, Term};

pub(super) fn interval(r: &Interval, depth: usize, nodes: &mut usize) -> Result<()> {
    limits(depth, nodes)?;
    match r {
        Interval::Var(n) if *n > 32 => return Err("dimension index exceeds 32".into()),
        Interval::Neg(a) => interval(a, depth + 1, nodes)?,
        Interval::Meet(a, b) | Interval::Join(a, b) => {
            interval(a, depth + 1, nodes)?;
            interval(b, depth + 1, nodes)?;
        }
        _ => {}
    }
    Ok(())
}
pub(super) fn face(f: &Face, depth: usize, nodes: &mut usize) -> Result<()> {
    limits(depth, nodes)?;
    match f {
        Face::End(n, _) if *n > 32 => return Err("face dimension index exceeds 32".into()),
        Face::And(a, b) | Face::Or(a, b) => {
            face(a, depth + 1, nodes)?;
            face(b, depth + 1, nodes)?;
        }
        _ => {}
    }
    Ok(())
}
fn limits(depth: usize, nodes: &mut usize) -> Result<()> {
    *nodes += 1;
    if depth > 32 || *nodes > 10_000 {
        return Err("cubical syntax exceeds depth 32 or 10000 nodes".into());
    }
    Ok(())
}
pub(super) fn term(t: &Term, depth: usize, nodes: &mut usize) -> Result<()> {
    limits(depth, nodes)?;
    match t {
        Term::Defined(def) => {
            for arg in def.arguments() {
                term(arg, depth + 1, nodes)?;
            }
        }
        Term::Universe(n) | Term::Var(n) if *n > 32 => {
            return Err("universe level or variable index exceeds 32".into());
        }
        Term::Pi(a, b)
        | Term::Sigma(a, b)
        | Term::Lam(a, b)
        | Term::App(a, b)
        | Term::PathLam(a, b) => {
            term(a, depth + 1, nodes)?;
            term(b, depth + 1, nodes)?;
        }
        Term::Path(a, b, c) | Term::Pair(a, b, c) | Term::Glue(a, b, c) => {
            term(a, depth + 1, nodes)?;
            term(b, depth + 1, nodes)?;
            term(c, depth + 1, nodes)?;
        }
        Term::Fst(p) | Term::Snd(p) | Term::Unglue(p) => term(p, depth + 1, nodes)?,
        Term::PathApp(p, r) => {
            term(p, depth + 1, nodes)?;
            interval(r, depth + 1, nodes)?;
        }
        Term::Comp(a, phi, tube, base) | Term::GlueType(a, phi, tube, base) => {
            term(a, depth + 1, nodes)?;
            face(phi, depth + 1, nodes)?;
            term(tube, depth + 1, nodes)?;
            term(base, depth + 1, nodes)?;
        }
        Term::System(ty, sides) => {
            if sides.len() > 16 {
                return Err("system exceeds 16 branches".into());
            }
            term(ty, depth + 1, nodes)?;
            for (f, t) in sides {
                face(f, depth + 1, nodes)?;
                term(t, depth + 1, nodes)?;
            }
        }
        _ => {}
    }
    Ok(())
}

pub(super) fn checked(t: &Term) -> Result<()> {
    term(t, 0, &mut 0)
}
