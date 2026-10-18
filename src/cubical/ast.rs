//! Annotated producer syntax. Annotations guide generation and are erased
//! from object terms; they are not new object-theory constructors.
use crate::sexp::{Sexp, atom, call};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Interval {
    Zero,
    One,
    Var(usize),
    Neg(Box<Interval>),
    Meet(Box<Interval>, Box<Interval>),
    Join(Box<Interval>, Box<Interval>),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Face {
    False,
    True,
    End(usize, bool),
    And(Box<Face>, Box<Face>),
    Or(Box<Face>, Box<Face>),
}

impl Face {
    pub fn quote(&self) -> Sexp {
        match self {
            Self::False => atom("ff"),
            Self::True => atom("ft"),
            Self::End(n, one) => call(if *one { "at1" } else { "at0" }, [number(*n)]),
            Self::And(a, b) => call("fand", [a.quote(), b.quote()]),
            Self::Or(a, b) => call("for", [a.quote(), b.quote()]),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Universe(usize),
    Var(usize),
    Nat,
    Zero,
    Pi(Box<Term>, Box<Term>),
    Lam(Box<Term>, Box<Term>),
    App(Box<Term>, Box<Term>),
    Path(Box<Term>, Box<Term>, Box<Term>),
    PathLam(Box<Term>, Box<Term>),
    PathApp(Box<Term>, Interval),
    System(Box<Term>, Vec<(Face, Term)>),
}

pub(super) fn number(n: usize) -> Sexp {
    (0..n).fold(atom("z"), |n, _| call("s", [n]))
}

impl Interval {
    pub fn quote(&self) -> Sexp {
        match self {
            Self::Zero => atom("i0"),
            Self::One => atom("i1"),
            Self::Var(n) => call("dim", [number(*n)]),
            Self::Neg(r) => call("neg", [r.quote()]),
            Self::Meet(r, s) => call("meet", [r.quote(), s.quote()]),
            Self::Join(r, s) => call("join", [r.quote(), s.quote()]),
        }
    }
}

impl Term {
    pub fn quote(&self) -> Sexp {
        match self {
            Self::Universe(l) => call("u", [number(*l)]),
            Self::Var(n) => call("v", [number(*n)]),
            Self::Nat => atom("nat"),
            Self::Zero => atom("zero"),
            Self::Pi(a, b) => call("pi", [a.quote(), b.quote()]),
            Self::Lam(_, body) => call("lam", [body.quote()]),
            Self::App(f, a) => call("app", [f.quote(), a.quote()]),
            Self::Path(a, b, c) => call("path", [a.quote(), b.quote(), c.quote()]),
            Self::PathLam(_, body) => call("plam", [body.quote()]),
            Self::PathApp(p, r) => call("papp", [p.quote(), r.quote()]),
            Self::System(_, sides) => call("system", [system(sides)]),
        }
    }
}

pub(super) fn context(g: &[Term]) -> Sexp {
    g.iter()
        .fold(atom("nil"), |tail, a| call("cons", [a.quote(), tail]))
}

pub(super) fn extend(g: &[Term], a: &Term) -> Vec<Term> {
    let mut out = g.to_vec();
    out.push(a.clone());
    out
}

pub(super) fn system(sides: &[(Face, Term)]) -> Sexp {
    sides.iter().rev().fold(atom("snil"), |tail, (f, t)| {
        call("side", [f.quote(), t.quote(), tail])
    })
}

impl Term {
    pub(super) fn has_system(&self) -> bool {
        match self {
            Self::System(..) => true,
            Self::Pi(a, b) | Self::Lam(a, b) | Self::App(a, b) | Self::PathLam(a, b) => {
                a.has_system() || b.has_system()
            }
            Self::Path(a, b, c) => a.has_system() || b.has_system() || c.has_system(),
            Self::PathApp(p, _) => p.has_system(),
            _ => false,
        }
    }
}
