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
    Sigma(Box<Term>, Box<Term>),
    Pair(Box<Term>, Box<Term>, Box<Term>),
    Fst(Box<Term>),
    Snd(Box<Term>),
    Lam(Box<Term>, Box<Term>),
    App(Box<Term>, Box<Term>),
    Path(Box<Term>, Box<Term>, Box<Term>),
    PathLam(Box<Term>, Box<Term>),
    PathApp(Box<Term>, Interval),
    System(Box<Term>, Vec<(Face, Term)>),
    Comp(Box<Term>, Face, Box<Term>, Box<Term>),
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
            Self::Sigma(a, b) => call("sigma", [a.quote(), b.quote()]),
            Self::Pair(_, a, b) => call("pair", [a.quote(), b.quote()]),
            Self::Fst(t) => call("fst", [t.quote()]),
            Self::Snd(t) => call("snd", [t.quote()]),
            Self::Lam(_, body) => call("lam", [body.quote()]),
            Self::App(f, a) => call("app", [f.quote(), a.quote()]),
            Self::Path(a, b, c) => call("path", [a.quote(), b.quote(), c.quote()]),
            Self::PathLam(_, body) => call("plam", [body.quote()]),
            Self::PathApp(p, r) => call("papp", [p.quote(), r.quote()]),
            Self::System(_, sides) => call("system", [system(sides)]),
            Self::Comp(a, phi, tube, base) => {
                call("comp", [a.quote(), phi.quote(), tube.quote(), base.quote()])
            }
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
    /// Source annotations participate in profile selection even when erased.
    fn any(&self, f: &impl Fn(&Self) -> bool) -> bool {
        f(self)
            || match self {
                Self::Pi(a, b)
                | Self::Sigma(a, b)
                | Self::Lam(a, b)
                | Self::App(a, b)
                | Self::PathLam(a, b) => a.any(f) || b.any(f),
                Self::Pair(a, b, c) | Self::Path(a, b, c) => a.any(f) || b.any(f) || c.any(f),
                Self::PathApp(p, _) | Self::Fst(p) | Self::Snd(p) => p.any(f),
                Self::System(ty, sides) => ty.any(f) || sides.iter().any(|(_, t)| t.any(f)),
                Self::Comp(a, _, tube, base) => a.any(f) || tube.any(f) || base.any(f),
                _ => false,
            }
    }

    pub(super) fn has_system(&self) -> bool {
        self.any(&|t| matches!(t, Self::System(..) | Self::Comp(..)))
    }

    pub(super) fn has_composition(&self) -> bool {
        self.any(&|t| matches!(t, Self::Comp(..)))
    }

    pub(super) fn has_sigma(&self) -> bool {
        self.any(&|t| {
            matches!(
                t,
                Self::Sigma(..) | Self::Pair(..) | Self::Fst(..) | Self::Snd(..)
            )
        })
    }
}
