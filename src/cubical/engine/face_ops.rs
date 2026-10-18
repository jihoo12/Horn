//! Untrusted syntax operations. Each result has a Horn derivation.
use super::{Op, PathProducer, natural, num, shape};
use crate::sexp::{Result, Sexp, atom, call};

impl PathProducer {
    pub fn boundary_syntax(&mut self, r: &Sexp) -> Result<(Sexp, Sexp, usize)> {
        let (a, b, rule, refs) = match shape(r)? {
            ("i0", []) => (atom("ft"), atom("ff"), "boundary.0", vec![]),
            ("i1", []) => (atom("ff"), atom("ft"), "boundary.1", vec![]),
            ("dim", [n]) => (
                call("at0", [n.clone()]),
                call("at1", [n.clone()]),
                "boundary.dim",
                vec![],
            ),
            ("neg", [s]) => {
                let (a, b, p) = self.boundary_syntax(s)?;
                (b, a, "boundary.neg", vec![p])
            }
            (op @ ("meet" | "join"), [s, t]) => {
                let (a, b, p) = self.boundary_syntax(s)?;
                let (c, d, q) = self.boundary_syntax(t)?;
                if op == "meet" {
                    (
                        call("for", [a, c]),
                        call("fand", [b, d]),
                        "boundary.meet",
                        vec![p, q],
                    )
                } else {
                    (
                        call("fand", [a, c]),
                        call("for", [b, d]),
                        "boundary.join",
                        vec![p, q],
                    )
                }
            }
            _ => return Err(format!("invalid interval: {r}")),
        };
        let id = self.p.emit(
            rule,
            refs,
            call("boundary", [r.clone(), a.clone(), b.clone()]),
        );
        Ok((a, b, id))
    }

    pub fn ftransform(&mut self, f: &Sexp, op: &Op) -> Result<(Sexp, usize)> {
        if !op.dimension() {
            return Err("face operations require a dimension operation".into());
        }
        let prefix = if op.replacement().is_some() {
            "fsubst"
        } else {
            "fshift"
        };
        let (head, args) = shape(f)?;
        let mut refs = vec![];
        let suffix;
        let out = match (head, args) {
            ("ff" | "ft", []) => {
                suffix = head;
                f.clone()
            }
            ("at0" | "at1", [n]) => {
                natural(n)?;
                suffix = if head == "at0" { "0" } else { "1" };
                let (r, p) = self.itransform(&call("dim", [n.clone()]), op)?;
                refs.push(p);
                if op.replacement().is_some() {
                    let (a, b, q) = self.boundary_syntax(&r)?;
                    refs.push(q);
                    if head == "at0" { a } else { b }
                } else {
                    let ("dim", [m]) = shape(&r)? else {
                        return Err("shifted literal is not a dimension".into());
                    };
                    call(head, [m.clone()])
                }
            }
            ("fand" | "for", [a, b]) => {
                suffix = if head == "fand" { "and" } else { "or" };
                let (a, p) = self.ftransform(a, op)?;
                let (b, q) = self.ftransform(b, op)?;
                refs.extend([p, q]);
                call(head, [a, b])
            }
            _ => return Err(format!("invalid face: {f}")),
        };
        let mut args = vec![f.clone(), num(op.cutoff())];
        if let Some(r) = op.replacement() {
            args.push(r.clone());
        }
        args.push(out.clone());
        let id = self
            .p
            .emit(&format!("{prefix}.{suffix}"), refs, call(prefix, args));
        Ok((out, id))
    }

    pub fn stransform(&mut self, s: &Sexp, op: &Op) -> Result<(Sexp, usize)> {
        let prefix = format!("s{}", op.prefix());
        let (out, suffix, refs) = match shape(s)? {
            ("snil", []) => (s.clone(), "nil", vec![]),
            ("side", [f, t, rest]) => {
                let mut refs = vec![];
                let f2 = if op.dimension() {
                    let (f2, id) = self.ftransform(f, op)?;
                    refs.push(id);
                    f2
                } else {
                    f.clone()
                };
                let (t2, id) = self.transform(t, op)?;
                refs.push(id);
                let (rest2, id) = self.stransform(rest, op)?;
                refs.push(id);
                (call("side", [f2, t2, rest2]), "side", refs)
            }
            _ => return Err(format!("invalid system: {s}")),
        };
        let mut args = vec![s.clone(), num(op.cutoff())];
        if let Some(r) = op.replacement() {
            args.push(r.clone());
        }
        args.push(out.clone());
        let id = self
            .p
            .emit(&format!("{prefix}.{suffix}"), refs, call(&prefix, args));
        Ok((out, id))
    }
}
