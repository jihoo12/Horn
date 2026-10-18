//! Untrusted definitional expansion of equivalences into Pi, Sigma and PathP.
//! There is no primitive Equiv or isEquiv term/type in the trusted signature.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{cons, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::sexp::{Result, Sexp, atom, call};

#[derive(Default)]
pub struct EquivalenceProducer {
    pub r: RestrictedProducer,
}
impl EquivalenceProducer {
    pub fn contr_type(&mut self, x: &Sexp) -> Result<(Sexp, usize)> {
        self.r.contr_type(x)
    }
    pub fn fiber_type(&mut self, a: &Sexp, b: &Sexp, f: &Sexp, y: &Sexp) -> Result<(Sexp, usize)> {
        self.r.fiber_type(a, b, f, y)
    }
    pub fn is_equiv_type(&mut self, a: &Sexp, b: &Sexp, f: &Sexp) -> Result<(Sexp, usize)> {
        self.r.is_equiv_type(a, b, f)
    }
    pub fn equiv_type(&mut self, a: &Sexp, b: &Sexp) -> Result<(Sexp, usize)> {
        self.r.equiv_type(a, b)
    }
}

pub fn equivalence_demo() -> Result<EquivalenceProducer> {
    let mut p = EquivalenceProducer::default();
    let nat = atom("nat");
    let nil = atom("nil");
    let top = Face::True;
    let (eqv, def) = p.equiv_type(&nat, &nat)?;
    p.r.f.path.p.result("equivalence-expansion", def);
    let id = p.r.export_has(0, &nil, &eqv, &u(0))?;
    p.r.f.path.p.result("closed-equivalence-type", id);

    let g = cons(u(0), cons(u(0), nil.clone()));
    let (eqv, _) = p.equiv_type(&v(1), &v(0))?;
    let id = p.r.export_has(0, &g, &eqv, &u(0))?;
    p.r.f.path.p.result("open-equivalence-type", id);

    let (contr, _) = p.contr_type(&nat)?;
    let id = p.r.export_has(0, &nil, &contr, &u(0))?;
    p.r.f.path.p.result("contractibility-type", id);
    let gf = cons(call("pi", [nat.clone(), nat.clone()]), nil.clone());
    let (fiber, _) = p.fiber_type(&nat, &nat, &v(0), &atom("zero"))?;
    let id = p.r.export_has(0, &gf, &fiber, &u(0))?;
    p.r.f.path.p.result("fiber-type", id);

    let sigma = call("sigma", [u(0), v(0)]);
    let pair = call("pair", [nat.clone(), atom("zero")]);
    let id = p.r.export_has(0, &nil, &pair, &sigma)?;
    p.r.f.path.p.result("dependent-pair", id);
    let id =
        p.r.equality(0, &nil, &top, &call("fst", [pair.clone()]), &nat, &u(0))?;
    p.r.f.path.p.result("fst-beta", id);
    let id =
        p.r.equality(0, &nil, &top, &call("snd", [pair]), &atom("zero"), &nat)?;
    p.r.f.path.p.result("dependent-snd-beta", id);
    Ok(p)
}
