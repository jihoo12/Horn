//! A genuine identity equivalence witness, expanded into the deep language.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{cons, dim, papp, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::sexp::{Result, Sexp, atom, call};

// In context A:U_l, the same ordinary core term works at every universe level.
// The contraction of (x,p) in fiber(id,y) is
//   <i> (p (~i), <j> p (~i \/ j)).
pub fn identity_equivalence() -> Sexp {
    let identity = call("lam", [v(0)]);
    let center = call("pair", [v(0), call("plam", [v(0)])]);
    let p = call("snd", [v(0)]);
    let first = papp(p.clone(), call("neg", [dim(0)]));
    let second = call(
        "plam",
        [papp(p, call("join", [call("neg", [dim(1)]), dim(0)]))],
    );
    let contraction = call("lam", [call("plam", [call("pair", [first, second])])]);
    call(
        "lam",
        [call(
            "pair",
            [identity, call("lam", [call("pair", [center, contraction])])],
        )],
    )
}

// The type parameter is erased in this term: this body contains no free
// ordinary variables or dimensions and is checked at each requested Equiv A A.
#[allow(dead_code)] // Used by ua-demo; the standalone identity demo checks the whole lambda.
pub fn identity_core() -> Sexp {
    let Sexp::List(mut xs) = identity_equivalence() else {
        unreachable!()
    };
    xs.remove(1)
}

pub fn identity_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    let nil = atom("nil");
    let g = cons(u(0), nil.clone());
    let (eqv, _) = p.equiv_type(&v(0), &v(0))?;
    let expected = call("pi", [u(0), eqv]);
    let witness = identity_equivalence();
    let id = p.export_has(0, &nil, &witness, &expected)?;
    p.f.path.p.result("identity-equivalence", id);
    // The witness is closed; no isEquiv or univalence assumption is in Γ.
    // Exercise its first projection after application to an arbitrary A.
    p.check(0, &g, &Face::True, &witness, &expected)?;
    let applied = call("app", [witness, v(0)]);
    let (_, id) = p.infer(0, &g, &Face::True, &applied)?;
    p.f.path.p.result("identity-equivalence-instance", id);
    Ok(p)
}
