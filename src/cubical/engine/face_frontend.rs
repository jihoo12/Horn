//! Untrusted face search. The kernel checks the emitted branching derivations.
use crate::cubical::engine::path_frontend::{Op, PathProducer, dim};
use crate::cubical::engine::term::{Result, Sexp, atom, call};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Face {
    False,
    True,
    End(usize, bool),
    And(Box<Face>, Box<Face>),
    Or(Box<Face>, Box<Face>),
}
impl Face {
    // Untrusted DNF antichain normalization. Callers must certify each use
    // through entails; this function is never part of the proof kernel.
    #[allow(dead_code)]
    pub fn normal(&self) -> Self {
        use std::collections::BTreeSet;
        type Clause = BTreeSet<(usize, bool)>;
        fn prune(mut clauses: Vec<Clause>) -> Vec<Clause> {
            clauses.sort();
            clauses.dedup();
            (0..clauses.len())
                .filter(|&i| {
                    !(0..clauses.len()).any(|j| i != j && clauses[j].is_subset(&clauses[i]))
                })
                .map(|i| clauses[i].clone())
                .collect()
        }
        fn dnf(f: &Face) -> Vec<Clause> {
            match f {
                Face::False => vec![],
                Face::True => vec![Clause::new()],
                Face::End(n, b) => vec![Clause::from([(*n, *b)])],
                Face::Or(a, b) => {
                    let mut out = dnf(a);
                    out.extend(dnf(b));
                    prune(out)
                }
                Face::And(a, b) => {
                    let mut out = vec![];
                    let bs = dnf(b);
                    for a in dnf(a) {
                        for b in &bs {
                            if a.iter().any(|(n, v)| b.contains(&(*n, !v))) {
                                continue;
                            }
                            out.push(a.union(b).copied().collect());
                        }
                    }
                    prune(out)
                }
            }
        }
        dnf(self)
            .into_iter()
            .map(|clause| {
                clause
                    .into_iter()
                    .map(|(n, b)| Self::End(n, b))
                    .reduce(Self::and)
                    .unwrap_or(Self::True)
            })
            .reduce(Self::or)
            .unwrap_or(Self::False)
    }
    #[allow(dead_code)] // The standalone face demo only produces, not parses, faces.
    pub fn parse(t: &Sexp) -> Result<Self> {
        Ok(match shape(t)? {
            ("ff", []) => Self::False,
            ("ft", []) => Self::True,
            ("at0", [n]) => Self::End(natural(n)?, false),
            ("at1", [n]) => Self::End(natural(n)?, true),
            ("fand", [a, b]) => Self::parse(a)?.and(Self::parse(b)?),
            ("for", [a, b]) => Self::parse(a)?.or(Self::parse(b)?),
            _ => return Err(format!("invalid face: {t}")),
        })
    }
    pub fn and(self, other: Self) -> Self {
        Self::And(Box::new(self), Box::new(other))
    }
    pub fn or(self, other: Self) -> Self {
        Self::Or(Box::new(self), Box::new(other))
    }
    pub fn quote(&self) -> Sexp {
        match self {
            Self::False => atom("ff"),
            Self::True => atom("ft"),
            Self::End(n, b) => call(if *b { "at1" } else { "at0" }, [number(*n)]),
            Self::And(a, b) => call("fand", [a.quote(), b.quote()]),
            Self::Or(a, b) => call("for", [a.quote(), b.quote()]),
        }
    }
}
fn number(n: usize) -> Sexp {
    (0..n).fold(atom("z"), |n, _| call("s", [n]))
}
fn context(fs: &[Face]) -> Sexp {
    fs.iter()
        .rev()
        .fold(atom("fnil"), |tail, f| call("fc", [f.quote(), tail]))
}
fn shape(t: &Sexp) -> Result<(&str, &[Sexp])> {
    match t {
        Sexp::Atom(a) => Ok((a, &[])),
        Sexp::List(xs) if !xs.is_empty() => Ok((xs[0].atom()?, &xs[1..])),
        _ => Err("empty interval expression".into()),
    }
}
fn natural(t: &Sexp) -> Result<usize> {
    match shape(t)? {
        ("z", []) => Ok(0),
        ("s", [n]) => Ok(natural(n)? + 1),
        _ => Err("invalid dimension index".into()),
    }
}

#[derive(Default)]
pub struct FaceProducer {
    pub path: PathProducer,
    entailments: std::collections::HashMap<Sexp, Result<usize>>,
}
impl FaceProducer {
    fn emit(&mut self, rule: &str, refs: Vec<usize>, j: Sexp) -> usize {
        self.path.p.emit(rule, refs, j)
    }
    /// `∀k. f` (CCHM 3): literals on dimension k become false, the others
    /// are kept with higher dimensions lowered. The result is the largest
    /// face without k that entails f.
    #[allow(dead_code)] // Used by Glue composition, not by every binary.
    pub fn forall(&mut self, f: &Face, k: usize) -> Result<(Face, usize)> {
        let end = |b: bool| if b { "1" } else { "0" };
        let (out, rule, refs) = match f {
            Face::False => (Face::False, "fforall.ff".to_owned(), vec![]),
            Face::True => (Face::True, "fforall.ft".to_owned(), vec![]),
            Face::End(n, b) if *n == k => (Face::False, format!("fforall.{}.hit", end(*b)), vec![]),
            Face::End(n, b) if *n < k => (
                f.clone(),
                format!("fforall.{}.lt", end(*b)),
                vec![self.path.comparison(*n, k, true)?],
            ),
            Face::End(n, b) => (
                Face::End(n - 1, *b),
                format!("fforall.{}.gt", end(*b)),
                vec![self.path.comparison(k, *n, true)?],
            ),
            Face::And(a, b) | Face::Or(a, b) => {
                let (a2, ai) = self.forall(a, k)?;
                let (b2, bi) = self.forall(b, k)?;
                if matches!(f, Face::And(..)) {
                    (a2.and(b2), "fforall.and".to_owned(), vec![ai, bi])
                } else {
                    (a2.or(b2), "fforall.or".to_owned(), vec![ai, bi])
                }
            }
        };
        let j = call("fforall", [f.quote(), number(k), out.quote()]);
        Ok((out, self.emit(&rule, refs, j)))
    }
    pub fn face(&mut self, d: usize, f: &Face) -> Result<usize> {
        if self.path.memoization_enabled()
            && let Some(id) = self
                .path
                .p
                .known_judgment(&call("face", [number(d), f.quote()]))
        {
            return Ok(id);
        }
        let (rule, refs) = match f {
            Face::False => ("face.ff", vec![]),
            Face::True => ("face.ft", vec![]),
            Face::End(n, b) => (
                if *b { "face.1" } else { "face.0" },
                vec![self.path.interval(d, &dim(*n))?],
            ),
            Face::And(a, b) => ("face.and", vec![self.face(d, a)?, self.face(d, b)?]),
            Face::Or(a, b) => ("face.or", vec![self.face(d, a)?, self.face(d, b)?]),
        };
        Ok(self.emit(rule, refs, call("face", [number(d), f.quote()])))
    }
    fn member(&mut self, fs: &[Face], i: usize) -> usize {
        let refs = if i == 0 {
            vec![]
        } else {
            vec![self.member(&fs[1..], i - 1)]
        };
        self.emit(
            if i == 0 {
                "member.here"
            } else {
                "member.there"
            },
            refs,
            call("member", [fs[i].quote(), context(fs)]),
        )
    }
    fn take(&mut self, fs: &[Face], i: usize) -> usize {
        let refs = if i == 0 {
            vec![]
        } else {
            vec![self.take(&fs[1..], i - 1)]
        };
        let mut rest = fs.to_vec();
        rest.remove(i);
        self.emit(
            if i == 0 { "take.here" } else { "take.there" },
            refs,
            call("take", [context(fs), fs[i].quote(), context(&rest)]),
        )
    }
    fn cover(&mut self, fs: &[Face], goal: &Face) -> Result<usize> {
        let j = call("cover", [context(fs), goal.quote()]);
        if *goal == Face::True {
            return Ok(self.emit("cover.top", vec![], j));
        }
        if let Some(i) = fs.iter().position(|f| f == goal) {
            let p = self.member(fs, i);
            return Ok(self.emit("cover.hit", vec![p], j));
        }
        if let Some(i) = fs.iter().position(|f| *f == Face::False) {
            let p = self.member(fs, i);
            return Ok(self.emit("cover.absurd", vec![p], j));
        }
        for (i, f) in fs.iter().enumerate() {
            if let Face::End(n, b) = f
                && let Some(k) = fs.iter().position(|g| *g == Face::End(*n, !b))
            {
                let (i, k) = if *b { (k, i) } else { (i, k) };
                let p = self.member(fs, i);
                let q = self.member(fs, k);
                return Ok(self.emit("cover.clash", vec![p, q], j));
            }
        }
        if let Some(i) = fs
            .iter()
            .position(|f| matches!(f, Face::And(..) | Face::Or(..)))
        {
            let take = self.take(fs, i);
            let mut rest = fs.to_vec();
            let f = rest.remove(i);
            let (rule, refs) = match f {
                Face::And(a, b) => {
                    let mut expanded = vec![*a, *b];
                    expanded.extend(rest);
                    ("cover.and-left", vec![take, self.cover(&expanded, goal)?])
                }
                Face::Or(a, b) => {
                    let mut left = vec![*a];
                    left.extend(rest.clone());
                    let mut right = vec![*b];
                    right.extend(rest);
                    (
                        "cover.or-left",
                        vec![take, self.cover(&left, goal)?, self.cover(&right, goal)?],
                    )
                }
                _ => unreachable!(),
            };
            return Ok(self.emit(rule, refs, j));
        }
        match goal {
            Face::And(a, b) => {
                let p = self.cover(fs, a)?;
                let q = self.cover(fs, b)?;
                Ok(self.emit("cover.and-right", vec![p, q], j))
            }
            Face::Or(a, b) => {
                if let Ok(p) = self.cover(fs, a) {
                    Ok(self.emit("cover.or-right0", vec![p], j))
                } else {
                    let q = self.cover(fs, b)?;
                    Ok(self.emit("cover.or-right1", vec![q], j))
                }
            }
            _ => Err(format!(
                "face implication does not hold: {} -> {goal:?}",
                context(fs)
            )),
        }
    }
    pub fn entails(&mut self, d: usize, a: &Face, b: &Face) -> Result<usize> {
        if self.path.memoization_enabled() {
            let key = call("entails", [number(d), a.quote(), b.quote()]);
            if let Some(result) = self.entailments.get(&key) {
                return result.clone();
            }
            let result = self.entails_search(d, a, b);
            self.entailments.insert(key, result.clone());
            return result;
        }
        self.entails_search(d, a, b)
    }
    fn entails_search(&mut self, d: usize, a: &Face, b: &Face) -> Result<usize> {
        let p = self.face(d, a)?;
        let q = self.face(d, b)?;
        let r = self.cover(std::slice::from_ref(a), b)?;
        Ok(self.emit(
            "entails.checked",
            vec![p, q, r],
            call("entails", [number(d), a.quote(), b.quote()]),
        ))
    }
    pub fn boundary(&mut self, r: &Sexp) -> Result<(Face, Face, usize)> {
        let (a, b, rule, refs) = match shape(r)? {
            ("i0", []) => (Face::True, Face::False, "boundary.0", vec![]),
            ("i1", []) => (Face::False, Face::True, "boundary.1", vec![]),
            ("dim", [n]) => {
                let n = natural(n)?;
                (
                    Face::End(n, false),
                    Face::End(n, true),
                    "boundary.dim",
                    vec![],
                )
            }
            ("neg", [s]) => {
                let (a, b, p) = self.boundary(s)?;
                (b, a, "boundary.neg", vec![p])
            }
            (op @ ("meet" | "join"), [s, t]) => {
                let (a, b, p) = self.boundary(s)?;
                let (c, d, q) = self.boundary(t)?;
                if op == "meet" {
                    (a.or(c), b.and(d), "boundary.meet", vec![p, q])
                } else {
                    (a.and(c), b.or(d), "boundary.join", vec![p, q])
                }
            }
            _ => return Err("unsupported interval expression".into()),
        };
        let p = self.emit(
            rule,
            refs,
            call("boundary", [r.clone(), a.quote(), b.quote()]),
        );
        Ok((a, b, p))
    }
    pub fn endpoint(&mut self, d: usize, phi: &Face, r: &Sexp, one: bool) -> Result<usize> {
        let i = self.path.interval(d, r)?;
        let (a, b, p) = self.boundary(r)?;
        let e = self.entails(d, phi, if one { &b } else { &a })?;
        Ok(self.emit(
            if one { "local.1" } else { "local.0" },
            vec![i, p, e],
            call(
                "local",
                [
                    number(d),
                    phi.quote(),
                    r.clone(),
                    atom(if one { "i1" } else { "i0" }),
                ],
            ),
        ))
    }
}

pub fn face_demo() -> Result<FaceProducer> {
    use Face::{End, True};
    let mut p = FaceProducer::default();
    let i0 = End(0, false);
    let i1 = End(0, true);
    let j0 = End(1, false);
    let j1 = End(1, true);
    let examples = [
        (
            "distribute",
            i0.clone().and(j0.clone().or(j1.clone())),
            i0.clone().and(j0.clone()).or(i0.clone().and(j1.clone())),
        ),
        ("inconsistent", i0.clone().and(i1.clone()), Face::False),
        ("boundary-cover", i0.clone().or(i1.clone()), True),
    ];
    for (name, a, b) in examples {
        let n = p.entails(2, &a, &b)?;
        p.path.p.result(name, n);
    }
    let ij = call("meet", [dim(0), dim(1)]);
    let n = p.endpoint(2, &i0.clone().or(j0), &ij, false)?;
    p.path.p.result("meet-zero", n);
    let n = p.endpoint(2, &i1.clone().and(j1), &ij, true)?;
    p.path.p.result("meet-one", n);
    let n = p.endpoint(
        1,
        &i0.clone().or(i1.clone()),
        &call("meet", [dim(0), call("neg", [dim(0)])]),
        false,
    )?;
    p.path.p.result("boundary-only", n);
    // x:Nat, p:Path Nat zero x. Show p i = zero under (i=0), not globally.
    let g = call(
        "cons",
        [
            call("path", [atom("nat"), atom("zero"), call("v", [number(0)])]),
            call("cons", [atom("nat"), atom("nil")]),
        ],
    );
    let path = call("v", [number(0)]);
    let ty = p.path.infer(1, &g, &path)?;
    // infer returns (type, certificate).
    let local = p.endpoint(1, &i0, &dim(0), false)?;
    let dr = p.path.transform(&atom("nat"), &Op::DSubst(0, dim(0)))?;
    let ds = p.path.transform(&atom("nat"), &Op::DSubst(0, atom("i0")))?;
    let ar = p.path.infer(1, &g, &atom("nat"))?;
    let left = call("papp", [path.clone(), dim(0)]);
    let mid = call("papp", [path.clone(), atom("i0")]);
    let n = p.emit(
        "req.pdim",
        vec![ty.1, local, dr.1, ds.1, ar.1],
        call(
            "req",
            [
                number(1),
                g.clone(),
                i0.quote(),
                left.clone(),
                mid.clone(),
                atom("nat"),
            ],
        ),
    );
    let (_, _, eq) = p.path.endpoint(1, &g, &path, false)?;
    let wf = p.face(1, &i0)?;
    let m = p.emit(
        "req.global",
        vec![wf, eq],
        call(
            "req",
            [
                number(1),
                g.clone(),
                i0.quote(),
                mid,
                atom("zero"),
                atom("nat"),
            ],
        ),
    );
    let n = p.emit(
        "req.trans",
        vec![n, m],
        call(
            "req",
            [number(1), g, i0.quote(), left, atom("zero"), atom("nat")],
        ),
    );
    p.path.p.result("path-local-endpoint", n);
    Ok(p)
}
