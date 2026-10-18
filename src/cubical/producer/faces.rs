//! Untrusted sequent search. Successful branches emit every member, take and
//! cover step; no truth table or normalization oracle can grant acceptance.
use super::{Face, Interval, Producer, Result, Sexp, call, number};
use crate::sexp::atom;

fn assumptions(fs: &[Face]) -> Sexp {
    fs.iter()
        .rev()
        .fold(atom("fnil"), |tail, f| call("fc", [f.quote(), tail]))
}

impl Producer {
    pub(super) fn face(&mut self, d: usize, f: &Face) -> Result<usize> {
        let (rule, refs) = match f {
            Face::False => ("face.ff", vec![]),
            Face::True => ("face.ft", vec![]),
            Face::End(n, one) => (
                if *one { "face.1" } else { "face.0" },
                vec![self.interval(d, &Interval::Var(*n))?],
            ),
            Face::And(a, b) => ("face.and", vec![self.face(d, a)?, self.face(d, b)?]),
            Face::Or(a, b) => ("face.or", vec![self.face(d, a)?, self.face(d, b)?]),
        };
        self.fact(rule, refs, "face", vec![number(d), f.quote()])
    }

    fn member(&mut self, fs: &[Face], i: usize) -> Result<usize> {
        let (rule, refs) = if i == 0 {
            ("member.here", vec![])
        } else {
            ("member.there", vec![self.member(&fs[1..], i - 1)?])
        };
        self.fact(rule, refs, "member", vec![fs[i].quote(), assumptions(fs)])
    }

    fn take(&mut self, fs: &[Face], i: usize) -> Result<usize> {
        let (rule, refs) = if i == 0 {
            ("take.here", vec![])
        } else {
            ("take.there", vec![self.take(&fs[1..], i - 1)?])
        };
        let mut rest = fs.to_vec();
        rest.remove(i);
        self.fact(
            rule,
            refs,
            "take",
            vec![assumptions(fs), fs[i].quote(), assumptions(&rest)],
        )
    }

    fn cover(&mut self, fs: &[Face], target: &Face, depth: usize) -> Result<usize> {
        self.face_work += 1;
        if depth > 128 || self.face_work > 20_000 {
            return Err("face search exceeded depth 128 or 20000 obligations".into());
        }
        let judgment = call("cover", [assumptions(fs), target.quote()]);
        if let Some(&id) = self.known.get(&judgment) {
            return Ok(id);
        }
        let (rule, refs) = if *target == Face::True {
            ("cover.top", vec![])
        } else if let Some(i) = fs.iter().position(|f| f == target) {
            ("cover.hit", vec![self.member(fs, i)?])
        } else if let Some(i) = fs.iter().position(|f| *f == Face::False) {
            ("cover.absurd", vec![self.member(fs, i)?])
        } else if let Some((zero, one)) = fs.iter().enumerate().find_map(|(i, f)| {
            if let Face::End(n, false) = f {
                fs.iter()
                    .position(|f| f == &Face::End(*n, true))
                    .map(|j| (i, j))
            } else {
                None
            }
        }) {
            (
                "cover.clash",
                vec![self.member(fs, zero)?, self.member(fs, one)?],
            )
        } else if let Some(i) = fs
            .iter()
            .position(|f| matches!(f, Face::And(..) | Face::Or(..)))
        {
            let extract = self.take(fs, i)?;
            let mut rest = fs.to_vec();
            match rest.remove(i) {
                Face::And(a, b) => {
                    let mut expanded = vec![*a, *b];
                    expanded.extend(rest);
                    (
                        "cover.and-left",
                        vec![extract, self.cover(&expanded, target, depth + 1)?],
                    )
                }
                Face::Or(a, b) => {
                    let mut left = vec![*a];
                    left.extend(rest.clone());
                    let mut right = vec![*b];
                    right.extend(rest);
                    (
                        "cover.or-left",
                        vec![
                            extract,
                            self.cover(&left, target, depth + 1)?,
                            self.cover(&right, target, depth + 1)?,
                        ],
                    )
                }
                _ => unreachable!("compound assumption"),
            }
        } else {
            match target {
                Face::And(a, b) => (
                    "cover.and-right",
                    vec![self.cover(fs, a, depth + 1)?, self.cover(fs, b, depth + 1)?],
                ),
                Face::Or(a, b) => match self.cover(fs, a, depth + 1) {
                    Ok(id) => ("cover.or-right0", vec![id]),
                    Err(_) => ("cover.or-right1", vec![self.cover(fs, b, depth + 1)?]),
                },
                _ => return Err("face implication is not established".into()),
            }
        };
        self.emit(rule, refs, judgment)
    }

    pub(super) fn entails(&mut self, d: usize, a: &Face, b: &Face) -> Result<usize> {
        let x = self.face(d, a)?;
        let y = self.face(d, b)?;
        let proof = self.cover(std::slice::from_ref(a), b, 0)?;
        self.fact(
            "entails.checked",
            vec![x, y, proof],
            "entails",
            vec![number(d), a.quote(), b.quote()],
        )
    }

    pub(super) fn boundary(&mut self, r: &Interval) -> Result<(Face, Face, usize)> {
        let (a, b, rule, refs) = match r {
            Interval::Zero => (Face::True, Face::False, "boundary.0", vec![]),
            Interval::One => (Face::False, Face::True, "boundary.1", vec![]),
            Interval::Var(n) => (
                Face::End(*n, false),
                Face::End(*n, true),
                "boundary.dim",
                vec![],
            ),
            Interval::Neg(r) => {
                let (a, b, id) = self.boundary(r)?;
                (b, a, "boundary.neg", vec![id])
            }
            Interval::Meet(left, right) | Interval::Join(left, right) => {
                let (a, b, x) = self.boundary(left)?;
                let (c, e, y) = self.boundary(right)?;
                if matches!(r, Interval::Meet(..)) {
                    (
                        Face::Or(Box::new(a), Box::new(c)),
                        Face::And(Box::new(b), Box::new(e)),
                        "boundary.meet",
                        vec![x, y],
                    )
                } else {
                    (
                        Face::And(Box::new(a), Box::new(c)),
                        Face::Or(Box::new(b), Box::new(e)),
                        "boundary.join",
                        vec![x, y],
                    )
                }
            }
        };
        let id = self.fact(
            rule,
            refs,
            "boundary",
            vec![r.quote(), a.quote(), b.quote()],
        )?;
        Ok((a, b, id))
    }

    fn local_endpoint(&mut self, d: usize, phi: &Face, r: &Interval, one: bool) -> Result<usize> {
        let interval = self.interval(d, r)?;
        let (a, b, boundary) = self.boundary(r)?;
        let entails = self.entails(d, phi, if one { &b } else { &a })?;
        self.fact(
            if one { "local.1" } else { "local.0" },
            vec![interval, boundary, entails],
            "local",
            vec![
                number(d),
                phi.quote(),
                r.quote(),
                if one { atom("i1") } else { atom("i0") },
            ],
        )
    }

    pub(super) fn local(
        &mut self,
        d: usize,
        phi: &Face,
        r: &Interval,
        s: &Interval,
    ) -> Result<usize> {
        let face = self.face(d, phi)?;
        let ri = self.interval(d, r)?;
        let si = self.interval(d, s)?;
        let judgment = call("local", [number(d), phi.quote(), r.quote(), s.quote()]);
        if let Some(&id) = self.known.get(&judgment) {
            return Ok(id);
        }
        if r == s {
            let refl = self.fact("i.refl", vec![], "ieq", vec![r.quote(), s.quote()])?;
            return self.emit("local.global", vec![face, ri, si, refl], judgment);
        }
        if matches!(s, Interval::Zero | Interval::One) {
            return self.local_endpoint(d, phi, r, *s == Interval::One);
        }
        if matches!(r, Interval::Zero | Interval::One) {
            let reverse = self.local_endpoint(d, phi, s, *r == Interval::One)?;
            return self.emit("local.sym", vec![reverse], judgment);
        }
        let congruence = match (r, s) {
            (Interval::Neg(a), Interval::Neg(b)) => {
                self.local(d, phi, a, b).map(|id| ("local.neg", vec![id]))
            }
            (Interval::Meet(a, b), Interval::Meet(c, e))
            | (Interval::Join(a, b), Interval::Join(c, e)) => {
                self.local(d, phi, a, c).and_then(|x| {
                    self.local(d, phi, b, e).map(|y| {
                        (
                            if matches!(r, Interval::Meet(..)) {
                                "local.meet"
                            } else {
                                "local.join"
                            },
                            vec![x, y],
                        )
                    })
                })
            }
            _ => Err("no structural local equality".into()),
        };
        if let Ok((rule, refs)) = congruence {
            return self.emit(rule, refs, judgment);
        }
        for one in [false, true] {
            if let Ok(x) = self.local_endpoint(d, phi, r, one)
                && let Ok(y) = self.local_endpoint(d, phi, s, one)
            {
                let endpoint = if one { Interval::One } else { Interval::Zero };
                let reverse = self.fact(
                    "local.sym",
                    vec![y],
                    "local",
                    vec![number(d), phi.quote(), endpoint.quote(), s.quote()],
                )?;
                return self.emit("local.trans", vec![x, reverse], judgment);
            }
        }
        Err("local interval equality is not established by endpoint or structural evidence".into())
    }
}
