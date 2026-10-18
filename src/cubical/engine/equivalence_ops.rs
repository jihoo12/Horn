//! Untrusted definitional macros; all results are certified.
use super::RestrictedProducer;
use crate::cubical::engine::path_frontend::{Op, path, v};
use crate::cubical::engine::term::{Result, Sexp, call};

impl RestrictedProducer {
    pub fn contr_type(&mut self, x: &Sexp) -> Result<(Sexp, usize)> {
        let (x1, p) = self.f.path.transform(x, &Op::Shift(0))?;
        let (x2, q) = self.f.path.transform(&x1, &Op::Shift(0))?;
        let (xi, s) = self.f.path.transform(&x2, &Op::DShift(0))?;
        let out = call("sigma", [x.clone(), call("pi", [x1, path(xi, v(1), v(0))])]);
        let id = self.f.path.p.emit(
            "def.contr",
            vec![p, q, s],
            call("contrdef", [x.clone(), out.clone()]),
        );
        Ok((out, id))
    }
    pub fn fiber_type(&mut self, a: &Sexp, b: &Sexp, f: &Sexp, y: &Sexp) -> Result<(Sexp, usize)> {
        let (b1, p) = self.f.path.transform(b, &Op::Shift(0))?;
        let (bi, q) = self.f.path.transform(&b1, &Op::DShift(0))?;
        let (f1, s) = self.f.path.transform(f, &Op::Shift(0))?;
        let (y1, t) = self.f.path.transform(y, &Op::Shift(0))?;
        let out = call("sigma", [a.clone(), path(bi, call("app", [f1, v(0)]), y1)]);
        let id = self.f.path.p.emit(
            "def.fiber",
            vec![p, q, s, t],
            call(
                "fiberdef",
                [a.clone(), b.clone(), f.clone(), y.clone(), out.clone()],
            ),
        );
        Ok((out, id))
    }
    pub fn is_equiv_type(&mut self, a: &Sexp, b: &Sexp, f: &Sexp) -> Result<(Sexp, usize)> {
        let (a1, p) = self.f.path.transform(a, &Op::Shift(0))?;
        let (b1, q) = self.f.path.transform(b, &Op::Shift(0))?;
        let (f1, s) = self.f.path.transform(f, &Op::Shift(0))?;
        let (fiber, t) = self.fiber_type(&a1, &b1, &f1, &v(0))?;
        let (contr, c) = self.contr_type(&fiber)?;
        let out = call("pi", [b.clone(), contr]);
        let id = self.f.path.p.emit(
            "def.isequiv",
            vec![p, q, s, t, c],
            call("isequivdef", [a.clone(), b.clone(), f.clone(), out.clone()]),
        );
        Ok((out, id))
    }
    pub fn equiv_type(&mut self, a: &Sexp, b: &Sexp) -> Result<(Sexp, usize)> {
        let (a1, p) = self.f.path.transform(a, &Op::Shift(0))?;
        let (b1, q) = self.f.path.transform(b, &Op::Shift(0))?;
        let (iseq, s) = self.is_equiv_type(&a1, &b1, &v(0))?;
        let out = call("sigma", [call("pi", [a.clone(), b1]), iseq]);
        let id = self.f.path.p.emit(
            "def.equiv",
            vec![p, q, s],
            call("equivdef", [a.clone(), b.clone(), out.clone()]),
        );
        Ok((out, id))
    }
}
