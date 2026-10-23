//! Moving a core term out of ordinary binders it does not use: the inverse
//! of shifting. The binder table covers the core's ordinary binders; a
//! caller keeps a result only if shifting it back gives the term again.
use super::data;
use super::path_frontend::{natural, shape, v};
use super::term::{Sexp, call};

/// `t` under `by` more binders than it needs, moved out of them: variables
/// at or above `by` (past the binders inside `t`) drop by `by`; `None` if
/// it uses one of them.
pub fn lower(t: &Sexp, by: usize) -> Option<Sexp> {
    go(t, by, 0)
}

fn go(t: &Sexp, by: usize, cut: usize) -> Option<Sexp> {
    if let Ok(("v", [n])) = shape(t) {
        let n = natural(n).ok()?;
        return match n {
            n if n < cut => Some(t.clone()),
            n if n < cut + by => None,
            n => Some(v(n - by)),
        };
    }
    match t {
        Sexp::Atom(_) => Some(t.clone()),
        Sexp::List(xs) => {
            let head = xs[0].atom().ok()?;
            let mut out = Vec::new();
            for (i, x) in xs[1..].iter().enumerate() {
                out.push(go(x, by, cut + binds(head, i))?);
            }
            Some(call(head, out))
        }
    }
}

/// The ordinary binders argument `k` of a core term with this head is under.
fn binds(head: &str, k: usize) -> usize {
    match (head, k) {
        ("pi" | "sigma", 1) | ("lam", 0) | ("bif" | "natrec", 0) => 1,
        _ => usize::from(data::motive_index(head) == Some(k)),
    }
}
