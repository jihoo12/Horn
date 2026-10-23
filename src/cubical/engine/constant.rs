//! Definitions as constants. A script's `def NAME TYPE TERM` becomes the
//! closed constant `def/NAME` with a generated theory fragment, appended to
//! the selected theory like a data declaration's:
//!
//! ```text
//! (rule rhas.def/NAME ((rctx ?d ?g ?phi) (rhas z nil ft TERM TYPE))
//!   (rhas ?d ?g ?phi def/NAME TYPE))
//! (rule req.delta.def/NAME ((rctx ?d ?g ?phi) (rhas z nil ft TERM TYPE))
//!   (req ?d ?g ?phi def/NAME TERM TYPE))
//! ```
//!
//! Both rules need the definition's own typing as a premise, so a constant
//! is usable only where `TERM : TYPE` is derived: reading `def/NAME` as
//! `TERM`, every generated rule is an instance of a valid one (weakening a
//! closed typing, reflexivity), and the extension is conservative. The
//! constant is closed, so every structural operation keeps it.
//!
//! Terms mention a definition by its constant instead of a copy of its
//! body, so they stay the size they are written at; the engine unfolds a
//! constant (δ) only where computation needs its body.
use super::term::{Sexp, atom};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Write;

#[derive(Clone)]
pub struct Constant {
    pub term: Sexp,
    pub ty: Sexp,
    /// The step proving `(rhas z nil ft TERM TYPE)`.
    pub proof: usize,
}

thread_local! {
    static CONSTANTS: RefCell<HashMap<String, Constant>> = RefCell::new(HashMap::new());
}

pub fn clear() {
    CONSTANTS.with(|c| c.borrow_mut().clear());
}

/// The constant's symbol for a definition name.
pub fn symbol(name: &str) -> String {
    format!("def/{name}")
}

/// Register a definition whose typing was proved by step `proof`; its
/// generated theory text.
pub fn define(name: &str, term: Sexp, ty: Sexp, proof: usize) -> (Sexp, String) {
    let c = symbol(name);
    let mut w = String::new();
    let _ = writeln!(w, "; def {name} (generated)");
    let _ = writeln!(w, "(ctor {c} () Tm)");
    let _ = writeln!(w, "(rule scope.{c} () (scoped ?d ?n {c}))");
    for (op, r) in [
        ("shift", ""),
        ("subst", " ?r"),
        ("dshift", ""),
        ("dsubst", " ?r"),
    ] {
        let _ = writeln!(w, "(rule {op}.{c} () ({op} {c} ?k{r} {c}))");
    }
    let premises = format!("(rctx ?d ?g ?phi) (rhas z nil ft {term} {ty})");
    let _ = writeln!(w, "(rule rhas.{c} ({premises}) (rhas ?d ?g ?phi {c} {ty}))");
    let _ = writeln!(
        w,
        "(rule req.delta.{c} ({premises}) (req ?d ?g ?phi {c} {term} {ty}))"
    );
    CONSTANTS.with(|m| {
        m.borrow_mut()
            .insert(c.clone(), Constant { term, ty, proof })
    });
    (atom(&c), w)
}

pub fn get(symbol: &str) -> Option<Constant> {
    CONSTANTS.with(|m| m.borrow().get(symbol).cloned())
}
