//! Certified source abbreviation lowering. Definitions expand to the SAME
//! Pi/Sigma/Path syntax. Their def.* facts are checked like every other step.
use super::{Definition, Judgment, Op, Producer, Request, Result, Term, syntax};

impl Producer {
    pub(super) fn expand_definition(&mut self, def: &Definition) -> Result<(Term, usize)> {
        use Definition::*;
        use Term::{App, Path, Pi, Sigma, Var};
        let (out, refs, rule) = match def {
            Contr(x) => {
                let (x1, a) = self.transform(x, &Op::Shift(0))?;
                let (x2, b) = self.transform(&x1, &Op::Shift(0))?;
                let (xi, c) = self.transform(&x2, &Op::DShift(0))?;
                (
                    Sigma(
                        Box::new(x.clone()),
                        Box::new(Pi(
                            Box::new(x1),
                            Box::new(Path(Box::new(xi), Box::new(Var(1)), Box::new(Var(0)))),
                        )),
                    ),
                    vec![a, b, c],
                    "def.contr",
                )
            }
            Fiber(a, b, f, y) => {
                let (b1, x) = self.transform(b, &Op::Shift(0))?;
                let (bi, z) = self.transform(&b1, &Op::DShift(0))?;
                let (f1, w) = self.transform(f, &Op::Shift(0))?;
                let (y1, v) = self.transform(y, &Op::Shift(0))?;
                (
                    Sigma(
                        Box::new(a.clone()),
                        Box::new(Path(
                            Box::new(bi),
                            Box::new(App(Box::new(f1), Box::new(Var(0)))),
                            Box::new(y1),
                        )),
                    ),
                    vec![x, z, w, v],
                    "def.fiber",
                )
            }
            IsEquiv(a, b, f) => {
                let (a1, x) = self.transform(a, &Op::Shift(0))?;
                let (b1, y) = self.transform(b, &Op::Shift(0))?;
                let (f1, z) = self.transform(f, &Op::Shift(0))?;
                let (fiber, u) = self.expand_definition(&Fiber(a1, b1, f1, Var(0)))?;
                let (contr, v) = self.expand_definition(&Contr(fiber))?;
                (
                    Pi(Box::new(b.clone()), Box::new(contr)),
                    vec![x, y, z, u, v],
                    "def.isequiv",
                )
            }
            Equiv(a, b) => {
                let (a1, x) = self.transform(a, &Op::Shift(0))?;
                let (b1, y) = self.transform(b, &Op::Shift(0))?;
                let (is_equiv, z) = self.expand_definition(&IsEquiv(a1, b1.clone(), Var(0)))?;
                (
                    Sigma(
                        Box::new(Pi(Box::new(a.clone()), Box::new(b1))),
                        Box::new(is_equiv),
                    ),
                    vec![x, y, z],
                    "def.equiv",
                )
            }
        };
        // Check every intermediate expansion before its output is duplicated
        // by another macro or recursively quoted. This bounds nested growth.
        syntax::checked(&out)?;
        let args = def
            .arguments()
            .into_iter()
            .map(Term::quote)
            .chain([out.quote()]);
        let id = self.fact(rule, refs, def.predicate(), args.collect())?;
        Ok((out, id))
    }

    fn lower_definition(&mut self, def: &Definition) -> Result<Definition> {
        use Definition::*;
        Ok(match def {
            Contr(x) => Contr(self.lower_term(x)?),
            Fiber(a, b, f, y) => Fiber(
                self.lower_term(a)?,
                self.lower_term(b)?,
                self.lower_term(f)?,
                self.lower_term(y)?,
            ),
            IsEquiv(a, b, f) => IsEquiv(
                self.lower_term(a)?,
                self.lower_term(b)?,
                self.lower_term(f)?,
            ),
            Equiv(a, b) => Equiv(self.lower_term(a)?, self.lower_term(b)?),
        })
    }

    fn lower_box(&mut self, t: &Term) -> Result<Box<Term>> {
        self.lower_term(t).map(Box::new)
    }

    fn lower_term(&mut self, t: &Term) -> Result<Term> {
        use Term::*;
        let out = match t {
            Defined(def) => {
                let def = self.lower_definition(def)?;
                self.expand_definition(&def)?.0
            }
            Universe(_) | Nat | Zero | Var(_) => t.clone(),
            Pi(a, b) => Pi(self.lower_box(a)?, self.lower_box(b)?),
            Sigma(a, b) => Sigma(self.lower_box(a)?, self.lower_box(b)?),
            Lam(a, b) => Lam(self.lower_box(a)?, self.lower_box(b)?),
            App(f, a) => App(self.lower_box(f)?, self.lower_box(a)?),
            Pair(ty, a, b) => Pair(self.lower_box(ty)?, self.lower_box(a)?, self.lower_box(b)?),
            Fst(p) => Fst(self.lower_box(p)?),
            Snd(p) => Snd(self.lower_box(p)?),
            Path(a, b, c) => Path(self.lower_box(a)?, self.lower_box(b)?, self.lower_box(c)?),
            PathLam(a, b) => PathLam(self.lower_box(a)?, self.lower_box(b)?),
            PathApp(p, r) => PathApp(self.lower_box(p)?, r.clone()),
            Comp(a, phi, tube, base) => Comp(
                self.lower_box(a)?,
                phi.clone(),
                self.lower_box(tube)?,
                self.lower_box(base)?,
            ),
            System(ty, sides) => System(
                self.lower_box(ty)?,
                sides
                    .iter()
                    .map(|(phi, t)| Ok((phi.clone(), self.lower_term(t)?)))
                    .collect::<Result<Vec<_>>>()?,
            ),
        };
        syntax::checked(&out)?;
        Ok(out)
    }

    pub(super) fn lower_request(&mut self, request: &Request) -> Result<Request> {
        let lower = |p: &mut Self| -> Result<Request> {
            use Judgment::*;
            let context = request
                .context
                .iter()
                .map(|t| p.lower_term(t))
                .collect::<Result<Vec<_>>>()?;
            let judgment = match &request.judgment {
                Definition {
                    definition,
                    expansion,
                } => Definition {
                    definition: p.lower_definition(definition)?,
                    expansion: p.lower_term(expansion)?,
                },
                Has { term, ty } => Has {
                    term: p.lower_term(term)?,
                    ty: p.lower_term(ty)?,
                },
                Equal { left, right, ty } => Equal {
                    left: p.lower_term(left)?,
                    right: p.lower_term(right)?,
                    ty: p.lower_term(ty)?,
                },
                RestrictedHas { face, term, ty } => RestrictedHas {
                    face: face.clone(),
                    term: p.lower_term(term)?,
                    ty: p.lower_term(ty)?,
                },
                RestrictedEqual {
                    face,
                    left,
                    right,
                    ty,
                } => RestrictedEqual {
                    face: face.clone(),
                    left: p.lower_term(left)?,
                    right: p.lower_term(right)?,
                    ty: p.lower_term(ty)?,
                },
                Entails { .. } | Local { .. } => request.judgment.clone(),
            };
            let out = Request {
                name: request.name.clone(),
                dimensions: request.dimensions,
                context,
                judgment,
            };
            super::validate(&out)?;
            Ok(out)
        };
        lower(self).map_err(|e| format!("{}: definition lowering: {e}", request.name))
    }

    /// Source expand assertions require well-typed arguments too. The object
    /// def.* predicates themselves specify syntactic expansion, not witnesses.
    pub(super) fn definition_arguments(
        &mut self,
        scope: (usize, &[Term]),
        def: &Definition,
    ) -> Result<()> {
        use Definition::*;
        let (d, g) = scope;
        self.ctx(d, g)?;
        match def {
            Contr(x) => {
                self.universe(d, g, x)?;
            }
            Equiv(a, b) | IsEquiv(a, b, _) | Fiber(a, b, _, _) => {
                self.universe(d, g, a)?;
                self.universe(d, g, b)?;
                if let IsEquiv(_, _, f) | Fiber(_, _, f, _) = def {
                    let (b1, _) = self.transform(b, &Op::Shift(0))?;
                    self.check(d, g, f, &Term::Pi(Box::new(a.clone()), Box::new(b1)))?;
                }
                if let Fiber(_, b, _, y) = def {
                    self.check(d, g, y, b)?;
                }
            }
        }
        Ok(())
    }
}
