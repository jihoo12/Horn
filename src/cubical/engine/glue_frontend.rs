//! Untrusted Glue primitive examples in the deep object language.
//! No ua/univalence lemma is used or claimed here.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::frontend::number;
use crate::cubical::engine::path_frontend::{Op, cons, u, v};
use crate::cubical::engine::restricted_frontend::RestrictedProducer;
use crate::sexp::{Result, atom, call};

pub fn glue_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    let nil = atom("nil");
    let nat = atom("nat");
    let zero = atom("zero");
    let top = Face::True;
    let end = Face::End(0, false);
    let empty_gt = call(
        "glue-type",
        [nat.clone(), atom("ff"), nat.clone(), zero.clone()],
    );
    let id = p.export_has(0, &nil, &empty_gt, &u(0))?;
    p.f.path.p.result("empty-glue-type", id);
    let empty = call("glue", [empty_gt.clone(), zero.clone(), zero.clone()]);
    let id = p.export_has(0, &nil, &empty, &empty_gt)?;
    p.f.path.p.result("empty-glue-intro", id);
    let id = p.equality(0, &nil, &top, &call("unglue", [empty]), &zero, &nat)?;
    p.f.path.p.result("empty-unglue-beta", id);

    // A genuine equivalence witness is a context parameter, not a postulate
    // that every function is an equivalence. The empty-face example above
    // needs no witness at all because its partial equivalence is unreachable.
    let (et, _) = p.equiv_type(&nat, &nat)?;
    let g = cons(et, nil);
    let gt = call("glue-type", [nat.clone(), end.quote(), nat.clone(), v(0)]);
    let id = p.export_has(1, &g, &gt, &u(0))?;
    p.f.path.p.result("boundary-glue-type", id);
    let mapped = call("app", [call("fst", [v(0)]), zero.clone()]);
    let value = call("glue", [gt.clone(), zero.clone(), mapped.clone()]);
    let id = p.export_has(1, &g, &value, &gt)?;
    p.f.path.p.result("boundary-glue-intro", id);
    let id = p.equality(1, &g, &top, &call("unglue", [value.clone()]), &mapped, &nat)?;
    p.f.path.p.result("unglue-beta", id);
    let id = p.equality(1, &g, &end, &gt, &nat, &u(0))?;
    p.f.path.p.result("glue-type-boundary", id);
    let id = p.equality(1, &g, &end, &value, &zero, &nat)?;
    p.f.path.p.result("glue-term-boundary", id);

    let (gt2, _) = p.f.path.transform(&gt, &Op::Shift(0))?;
    let gv = cons(gt, g);
    let mapped_v = call("app", [call("fst", [v(1)]), v(0)]);
    let id = p.equality(1, &gv, &end, &call("unglue", [v(0)]), &mapped_v, &nat)?;
    p.f.path.p.result("unglue-boundary", id);
    let (_, vi) = p.infer(1, &gv, &top, &v(0))?;
    let rebuilt = call("glue", [gt2.clone(), v(0), call("unglue", [v(0)])]);
    let bi = p.check(1, &gv, &top, &rebuilt, &gt2)?;
    let id = p.f.path.p.emit(
        "req.glue-eta",
        vec![vi, bi],
        call("req", [number(1), gv, atom("ft"), rebuilt, v(0), gt2]),
    );
    p.f.path.p.result("glue-eta", id);
    Ok(p)
}
