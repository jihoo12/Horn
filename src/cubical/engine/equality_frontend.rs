//! Partial, untrusted congruence and interval simplification search.
//! All successful branches emit only deep object-theory derivations.
use super::{RestrictedProducer, level, shape};
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::frontend::number;
use crate::cubical::engine::path_frontend::{Op, cons, dim, papp};
use crate::cubical::engine::term::{Result, Sexp, atom, call};

impl RestrictedProducer {
    fn ieq(&mut self, rule: &str, refs: Vec<usize>, a: &Sexp, b: &Sexp) -> usize {
        self.f
            .path
            .p
            .emit(rule, refs, call("ieq", [a.clone(), b.clone()]))
    }
    pub fn interval_normal(&mut self, r: &Sexp) -> Result<(Sexp, usize)> {
        let (out, proof) = match shape(r)? {
            ("i0" | "i1", []) | ("dim", [_]) => {
                return Ok((r.clone(), self.ieq("i.refl", vec![], r, r)));
            }
            ("neg", [t]) => {
                let (t2, ti) = self.interval_normal(t)?;
                let mid = call("neg", [t2.clone()]);
                let p = self.ieq("i.neg-cong", vec![ti], r, &mid);
                let (out, rule) = if t2 == atom("i0") {
                    (atom("i1"), "i.neg-zero")
                } else if t2 == atom("i1") {
                    (atom("i0"), "i.neg-one")
                } else if let ("neg", [inner]) = shape(&t2)? {
                    (inner.clone(), "i.involution")
                } else {
                    return Ok((mid, p));
                };
                let q = self.ieq(rule, vec![], &mid, &out);
                (out, (p, q))
            }
            (op @ ("meet" | "join"), [a, b]) => {
                let (a2, ai) = self.interval_normal(a)?;
                let (b2, bi) = self.interval_normal(b)?;
                let mid = call(op, [a2.clone(), b2.clone()]);
                let p = self.ieq(&format!("i.{op}-cong"), vec![ai, bi], r, &mid);
                let (out, law, swapped) = if a2 == b2 {
                    (a2.clone(), "idem", false)
                } else if b2 == atom("i0") {
                    (
                        if op == "meet" { atom("i0") } else { a2.clone() },
                        "zero",
                        false,
                    )
                } else if b2 == atom("i1") {
                    (
                        if op == "meet" { a2.clone() } else { atom("i1") },
                        "one",
                        false,
                    )
                } else if a2 == atom("i0") {
                    (
                        if op == "meet" { atom("i0") } else { b2.clone() },
                        "zero",
                        true,
                    )
                } else if a2 == atom("i1") {
                    (
                        if op == "meet" { b2.clone() } else { atom("i1") },
                        "one",
                        true,
                    )
                } else {
                    return Ok((mid, p));
                };
                let q = if swapped {
                    let swapped = call(op, [b2, a2]);
                    let c = self.ieq(&format!("i.{op}-comm"), vec![], &mid, &swapped);
                    let l = self.ieq(&format!("i.{op}-{law}"), vec![], &swapped, &out);
                    self.ieq("i.trans", vec![c, l], &mid, &out)
                } else {
                    self.ieq(&format!("i.{op}-{law}"), vec![], &mid, &out)
                };
                (out, (p, q))
            }
            _ => return Err(format!("unsupported interval: {r}")),
        };
        let p = self.ieq("i.trans", vec![proof.0, proof.1], r, &out);
        Ok((out, p))
    }
    fn restricted_interval_normal(
        &mut self,
        d: usize,
        phi: &Face,
        r: &Sexp,
    ) -> Result<(Sexp, usize)> {
        let judgment =
            |a: &Sexp, b: &Sexp| call("local", [number(d), phi.quote(), a.clone(), b.clone()]);
        for one in [false, true] {
            if let Ok(eq) = self.f.endpoint(d, phi, r, one) {
                return Ok((atom(if one { "i1" } else { "i0" }), eq));
            }
        }
        let (mid, first) = match shape(r)? {
            (op @ ("meet" | "join"), [a, b]) => {
                let (a2, ai) = self.restricted_interval_normal(d, phi, a)?;
                let (b2, bi) = self.restricted_interval_normal(d, phi, b)?;
                let mid = call(op, [a2, b2]);
                let eq =
                    self.f
                        .path
                        .p
                        .emit(&format!("local.{op}"), vec![ai, bi], judgment(r, &mid));
                (mid, eq)
            }
            ("neg", [a]) => {
                let (a2, ai) = self.restricted_interval_normal(d, phi, a)?;
                let mid = call("neg", [a2]);
                let eq = self.f.path.p.emit("local.neg", vec![ai], judgment(r, &mid));
                (mid, eq)
            }
            _ => {
                let (out, eq) = self.interval_normal(r)?;
                let fi = self.f.face(d, phi)?;
                let ar = self.f.path.interval(d, r)?;
                let br = self.f.path.interval(d, &out)?;
                let eq =
                    self.f
                        .path
                        .p
                        .emit("local.global", vec![fi, ar, br, eq], judgment(r, &out));
                return Ok((out, eq));
            }
        };
        let (out, eq) = self.interval_normal(&mid)?;
        let fi = self.f.face(d, phi)?;
        let ar = self.f.path.interval(d, &mid)?;
        let br = self.f.path.interval(d, &out)?;
        let second = self
            .f
            .path
            .p
            .emit("local.global", vec![fi, ar, br, eq], judgment(&mid, &out));
        let eq = self
            .f
            .path
            .p
            .emit("local.trans", vec![first, second], judgment(r, &out));
        Ok((out, eq))
    }

    pub fn local_interval(&mut self, d: usize, phi: &Face, a: &Sexp, b: &Sexp) -> Result<usize> {
        let (aa, ai) = self.interval_normal(a)?;
        let (bb, bi) = self.interval_normal(b)?;
        if aa == bb {
            let sym = self.ieq("i.sym", vec![bi], &bb, b);
            let eq = self.ieq("i.trans", vec![ai, sym], a, b);
            let fi = self.f.face(d, phi)?;
            let ar = self.f.path.interval(d, a)?;
            let br = self.f.path.interval(d, b)?;
            return Ok(self.f.path.p.emit(
                "local.global",
                vec![fi, ar, br, eq],
                call("local", [number(d), phi.quote(), a.clone(), b.clone()]),
            ));
        }
        // The two intervals may agree only under this face restriction.
        for one in [false, true] {
            if let (Ok(ai), Ok(bi)) = (
                self.f.endpoint(d, phi, a, one),
                self.f.endpoint(d, phi, b, one),
            ) {
                let end = atom(if one { "i1" } else { "i0" });
                let sym = self.f.path.p.emit(
                    "local.sym",
                    vec![bi],
                    call("local", [number(d), phi.quote(), end, b.clone()]),
                );
                return Ok(self.f.path.p.emit(
                    "local.trans",
                    vec![ai, sym],
                    call("local", [number(d), phi.quote(), a.clone(), b.clone()]),
                ));
            }
        }
        let (aa, ai) = self.restricted_interval_normal(d, phi, a)?;
        let (bb, bi) = self.restricted_interval_normal(d, phi, b)?;
        if aa == bb {
            let sym = self.f.path.p.emit(
                "local.sym",
                vec![bi],
                call("local", [number(d), phi.quote(), bb, b.clone()]),
            );
            return Ok(self.f.path.p.emit(
                "local.trans",
                vec![ai, sym],
                call("local", [number(d), phi.quote(), a.clone(), b.clone()]),
            ));
        }
        Err(format!("interval equality search failed: {a} versus {b}"))
    }

    pub fn congruence(
        &mut self,
        d: usize,
        g: &Sexp,
        phi: &Face,
        a: &Sexp,
        b: &Sexp,
        ty: &Sexp,
    ) -> Result<usize> {
        let (ah, ax) = shape(a)?;
        let (bh, bx) = shape(b)?;
        let (th, tx) = shape(ty)?;
        // Eta is expanded only on one side. Both-pair/both-plam cases below
        // compare the components/bodies, so this search cannot eta-loop.
        if ah == "lam" && bh != "lam" && th == "pi" {
            let bi = self.check(d, g, phi, b, ty)?;
            let (b2, shift) = self.f.path.transform(b, &Op::Shift(0))?;
            let rebuilt = call(
                "lam",
                [call(
                    "app",
                    [b2, crate::cubical::engine::path_frontend::v(0)],
                )],
            );
            let ri = self.check(d, g, phi, &rebuilt, ty)?;
            let eta = self.eq(
                d,
                g,
                phi,
                &rebuilt,
                b,
                ty,
                "req.fun-eta",
                vec![bi, shift, ri],
            );
            let left = self.equality(d, g, phi, a, &rebuilt, ty)?;
            return Ok(self.eq(d, g, phi, a, b, ty, "req.trans", vec![left, eta]));
        }
        if ah == "glue" && bh != "glue" && th == "glue-type" {
            let bi = self.check(d, g, phi, b, ty)?;
            let rebuilt = call("glue", [ty.clone(), b.clone(), call("unglue", [b.clone()])]);
            let ri = self.check(d, g, phi, &rebuilt, ty)?;
            let eta = self.eq(d, g, phi, &rebuilt, b, ty, "req.glue-eta", vec![bi, ri]);
            let left = self.equality(d, g, phi, a, &rebuilt, ty)?;
            return Ok(self.eq(d, g, phi, a, b, ty, "req.trans", vec![left, eta]));
        }
        if ah == "pair" && bh != "pair" && th == "sigma" {
            let bi = self.check(d, g, phi, b, ty)?;
            let rebuilt = call("pair", [call("fst", [b.clone()]), call("snd", [b.clone()])]);
            let ri = self.check(d, g, phi, &rebuilt, ty)?;
            let eta = self.eq(d, g, phi, &rebuilt, b, ty, "req.pair-eta", vec![bi, ri]);
            let left = self.equality(d, g, phi, a, &rebuilt, ty)?;
            return Ok(self.eq(d, g, phi, a, b, ty, "req.trans", vec![left, eta]));
        }
        if ah == "plam" && bh != "plam" && th == "path" {
            let bi = self.check(d, g, phi, b, ty)?;
            let (b2, shift) = self.f.path.transform(b, &Op::DShift(0))?;
            let rebuilt = call("plam", [papp(b2, dim(0))]);
            let ri = self.check(d, g, phi, &rebuilt, ty)?;
            let eta = self.eq(
                d,
                g,
                phi,
                &rebuilt,
                b,
                ty,
                "req.path-eta",
                vec![bi, shift, ri],
            );
            let left = self.equality(d, g, phi, a, &rebuilt, ty)?;
            return Ok(self.eq(d, g, phi, a, b, ty, "req.trans", vec![left, eta]));
        }
        if (bh == "lam" && ah != "lam" && th == "pi")
            || (bh == "glue" && ah != "glue" && th == "glue-type")
            || (bh == "pair" && ah != "pair" && th == "sigma")
            || (bh == "plam" && ah != "plam" && th == "path")
        {
            let eq = self.equality(d, g, phi, b, a, ty)?;
            return Ok(self.eq(d, g, phi, a, b, ty, "req.sym", vec![eq]));
        }
        if let Some(eq) = self.congruence_circle(d, g, phi, a, b, ty)? {
            return Ok(eq);
        }
        if let Some(eq) = self.congruence_declared(d, g, phi, a, b, ty)? {
            return Ok(eq);
        }
        if ah != bh {
            return Err(format!(
                "local equality search failed: {a} versus {b} : {ty} under {} in {d} dimensions",
                phi.quote()
            ));
        }
        let (rule, refs) = match (ah, ax, bx, th, tx) {
            ("comp", [af, face, at, ab], [bf, other_face, bt, bb], _, _) => {
                let (out, ai) = self.infer(d, g, phi, a)?;
                let bi = self.check(d, g, phi, b, &out)?;
                let (g2, gi) = self.f.path.dshiftctx(g, 0)?;
                let (phi2, phii) = self.f.path.ftransform(&phi.quote(), &Op::DShift(0))?;
                let (face2, facei) = self.f.path.ftransform(face, &Op::DShift(0))?;
                let phi2 = Face::parse(&phi2)?;
                let (ua, _) = self.infer(d + 1, &g2, &phi2, af)?;
                level(&ua)?;
                let family = self.equality(d + 1, &g2, &phi2, af, bf, &ua)?;
                let tube =
                    self.equality(d + 1, &g2, &phi2.and(Face::parse(&face2)?), at, bt, af)?;
                let (a0, a0i) = self.f.path.transform(af, &Op::DSubst(0, atom("i0")))?;
                let base = self.equality(d, g, phi, ab, bb, &a0)?;
                let (rule, refs) = if face == other_face {
                    (
                        "req.comp-cong",
                        vec![ai, bi, gi, phii, facei, family, tube, a0i, base],
                    )
                } else {
                    let left = Face::parse(face)?;
                    let right = Face::parse(other_face)?;
                    let lr = self.f.entails(d, &phi.clone().and(left.clone()), &right)?;
                    let rl = self.f.entails(d, &phi.clone().and(right), &left)?;
                    (
                        "req.comp-face-cong",
                        vec![ai, bi, lr, rl, gi, phii, facei, family, tube, a0i, base],
                    )
                };
                let eq = self.eq(d, g, phi, a, b, &out, rule, refs);
                return self.retype_eq(d, g, phi, a, b, &out, ty, eq);
            }
            ("glue", [gt, au, av], [other_gt, bu, bv], "glue-type", [base, face, partial, _])
                if gt == other_gt && gt == ty =>
            {
                let ai = self.check(d, g, phi, a, ty)?;
                let bi = self.check(d, g, phi, b, ty)?;
                let ue =
                    self.equality(d, g, &phi.clone().and(Face::parse(face)?), au, bu, partial)?;
                let ve = self.equality(d, g, phi, av, bv, base)?;
                ("req.glue-cong", vec![ai, bi, ue, ve])
            }
            ("glue-type", [aa, aphi, at, ae], [ba, bphi, bt, be], "u", [_]) => {
                let ai = self.check(d, g, phi, a, ty)?;
                let bi = self.check(d, g, phi, b, ty)?;
                let base = self.equality(d, g, phi, aa, ba, ty)?;
                let left = Face::parse(aphi)?;
                let right = Face::parse(bphi)?;
                let lr = self.f.entails(d, &phi.clone().and(left.clone()), &right)?;
                let rl = self.f.entails(d, &phi.clone().and(right), &left)?;
                let under = phi.clone().and(left);
                let partial = self.equality(d, g, &under, at, bt, ty)?;
                let (et, def) = self.equiv_type(at, aa)?;
                let equiv = self.equality(d, g, &under, ae, be, &et)?;
                (
                    "req.glue-type-cong",
                    vec![ai, bi, base, lr, rl, partial, def, equiv],
                )
            }
            ("suc", [at], [bt], _, _) => {
                let nat = atom("nat");
                let eq = self.equality(d, g, phi, at, bt, &nat)?;
                let eq = self.eq(d, g, phi, a, b, &nat, "req.suc-cong", vec![eq]);
                return self.retype_eq(d, g, phi, a, b, &nat, ty, eq);
            }
            ("natrec", [ap, az, af, am], [bp, bz, bf, bm], _, _)
                if ap == bp && az == bz && af == bf =>
            {
                let ai = self.check(d, g, phi, a, ty)?;
                let bi = self.check(d, g, phi, b, ty)?;
                let eq = self.equality(d, g, phi, am, bm, &atom("nat"))?;
                return Ok(self.eq(d, g, phi, a, b, ty, "req.natrec-cong", vec![ai, bi, eq]));
            }
            ("bif", [ap, at, af, ab], [bp, bt, bf, bb], _, _)
                if ap == bp && at == bt && af == bf =>
            {
                // Same motive and branches: only the scrutinee may differ.
                let ai = self.check(d, g, phi, a, ty)?;
                let bi = self.check(d, g, phi, b, ty)?;
                let bool = atom("bool");
                let gb = crate::cubical::engine::path_frontend::cons(bool.clone(), g.clone());
                let (up, pi) = self.infer(d, &gb, phi, ap)?;
                let ep = self.eq(d, &gb, phi, ap, ap, &up, "req.refl", vec![pi]);
                let mut refs = vec![ai, bi, ep];
                for (branch, value) in [("btrue", at), ("bfalse", af)] {
                    let (pv, si) = self.f.path.transform(ap, &Op::Subst(0, atom(branch)))?;
                    let vi = self.check(d, g, phi, value, &pv)?;
                    let ev = self.eq(d, g, phi, value, value, &pv, "req.refl", vec![vi]);
                    refs.extend([si, ev]);
                }
                refs.push(self.equality(d, g, phi, ab, bb, &bool)?);
                return Ok(self.eq(d, g, phi, a, b, ty, "req.bif-cong", refs));
            }
            ("unglue", [at], [bt], _, _) => {
                let (gt, _) = self.infer(d, g, phi, at)?;
                let ("glue-type", [base, _, _, _]) = shape(&gt)? else {
                    return Err("unglue congruence expects Glue".into());
                };
                let eq = self.equality(d, g, phi, at, bt, &gt)?;
                let ai = self.check(d, g, phi, a, base)?;
                let bi = self.check(d, g, phi, b, base)?;
                let eq = self.eq(d, g, phi, a, b, base, "req.unglue-cong", vec![eq, ai, bi]);
                return self.retype_eq(d, g, phi, a, b, base, ty, eq);
            }
            (head @ ("pi" | "sigma"), [aa, ab], [ba, bb], "u", [_]) => {
                let ai = self.check(d, g, phi, a, ty)?;
                let bi = self.check(d, g, phi, b, ty)?;
                let (ua, _) = self.infer(d, g, phi, aa)?;
                level(&ua)?;
                let ae = self.equality(d, g, phi, aa, ba, &ua)?;
                let g2 = cons(aa.clone(), g.clone());
                let (ub, _) = self.infer(d, &g2, phi, ab)?;
                level(&ub)?;
                let be = self.equality(d, &g2, phi, ab, bb, &ub)?;
                (
                    if head == "pi" {
                        "req.pi-cong"
                    } else {
                        "req.sigma-cong"
                    },
                    vec![ai, bi, ae, be],
                )
            }
            ("lam", [body], [other], "pi", [dom, cod]) => {
                let ai = self.check(d, g, phi, a, ty)?;
                let bi = self.check(d, g, phi, b, ty)?;
                let eq = self.equality(d, &cons(dom.clone(), g.clone()), phi, body, other, cod)?;
                ("req.lam-cong", vec![ai, bi, eq])
            }
            ("pair", [a0, a1], [b0, b1], "sigma", [dom, cod]) => {
                let ai = self.check(d, g, phi, a, ty)?;
                let bi = self.check(d, g, phi, b, ty)?;
                let e0 = self.equality(d, g, phi, a0, b0, dom)?;
                let (bt, si) = self.f.path.transform(cod, &Op::Subst(0, a0.clone()))?;
                let e1 = self.equality(d, g, phi, a1, b1, &bt)?;
                ("req.pair-cong", vec![ai, bi, e0, si, e1])
            }
            ("path", [af, a0, a1], [bf, b0, b1], "u", [_]) => {
                let ai = self.check(d, g, phi, a, ty)?;
                let bi = self.check(d, g, phi, b, ty)?;
                let (g2, gi) = self.f.path.dshiftctx(g, 0)?;
                let (phi2, phii) = self.f.path.ftransform(&phi.quote(), &Op::DShift(0))?;
                let ef = self.equality(d + 1, &g2, &Face::parse(&phi2)?, af, bf, ty)?;
                let (at0, s0) = self.f.path.transform(af, &Op::DSubst(0, atom("i0")))?;
                let (at1, s1) = self.f.path.transform(af, &Op::DSubst(0, atom("i1")))?;
                let e0 = self.equality(d, g, phi, a0, b0, &at0)?;
                let e1 = self.equality(d, g, phi, a1, b1, &at1)?;
                ("req.path-cong", vec![ai, bi, gi, phii, ef, s0, s1, e0, e1])
            }
            ("plam", [body], [other], "path", [family, _, _]) => {
                let ai = self.check(d, g, phi, a, ty)?;
                let bi = self.check(d, g, phi, b, ty)?;
                let (g2, gi) = self.f.path.dshiftctx(g, 0)?;
                let (phi2, phii) = self.f.path.ftransform(&phi.quote(), &Op::DShift(0))?;
                let e = self.equality(d + 1, &g2, &Face::parse(&phi2)?, body, other, family)?;
                ("req.plam-cong", vec![ai, bi, gi, phii, e])
            }
            ("app", [af, aa], [bf, ba], _, _) => {
                let (ft, _) = self.infer(d, g, phi, af)?;
                let ("pi", [dom, cod]) = shape(&ft)? else {
                    return Err("application congruence expects Pi".into());
                };
                let ef = self.equality(d, g, phi, af, bf, &ft)?;
                let ea = self.equality(d, g, phi, aa, ba, dom)?;
                let (bt, si) = self.f.path.transform(cod, &Op::Subst(0, aa.clone()))?;
                let ai = self.check(d, g, phi, a, &bt)?;
                let bi = self.check(d, g, phi, b, &bt)?;
                let eq = self.eq(
                    d,
                    g,
                    phi,
                    a,
                    b,
                    &bt,
                    "req.app-cong",
                    vec![ef, ea, si, ai, bi],
                );
                return self.retype_eq(d, g, phi, a, b, &bt, ty, eq);
            }
            (head @ ("fst" | "snd"), [at], [bt], _, _) => {
                let (pt, _) = self.infer(d, g, phi, at)?;
                let ("sigma", [dom, cod]) = shape(&pt)? else {
                    return Err("projection congruence expects Sigma".into());
                };
                let e = self.equality(d, g, phi, at, bt, &pt)?;
                let mut refs = vec![e];
                let result_ty = if head == "fst" {
                    dom.clone()
                } else {
                    let (bt, si) = self
                        .f
                        .path
                        .transform(cod, &Op::Subst(0, call("fst", [at.clone()])))?;
                    refs.push(si);
                    bt
                };
                refs.push(self.check(d, g, phi, a, &result_ty)?);
                refs.push(self.check(d, g, phi, b, &result_ty)?);
                let eq = self.eq(
                    d,
                    g,
                    phi,
                    a,
                    b,
                    &result_ty,
                    if head == "fst" {
                        "req.fst-cong"
                    } else {
                        "req.snd-cong"
                    },
                    refs,
                );
                return self.retype_eq(d, g, phi, a, b, &result_ty, ty, eq);
            }
            ("papp", [ap, ar], [bp, br], _, _) => {
                let (pt, _) = self.infer(d, g, phi, ap)?;
                let ("path", [family, _, _]) = shape(&pt)? else {
                    return Err("path congruence expects PathP".into());
                };
                let ep = self.equality(d, g, phi, ap, bp, &pt)?;
                let er = self.local_interval(d, phi, ar, br)?;
                let (at, si) = self.f.path.transform(family, &Op::DSubst(0, ar.clone()))?;
                let ai = self.check(d, g, phi, a, &at)?;
                let bi = self.check(d, g, phi, b, &at)?;
                let eq = self.eq(
                    d,
                    g,
                    phi,
                    a,
                    b,
                    &at,
                    "req.papp-cong",
                    vec![ep, er, si, ai, bi],
                );
                return self.retype_eq(d, g, phi, a, b, &at, ty, eq);
            }
            _ => return Err(format!("congruence search failed: {a} versus {b} : {ty}")),
        };
        Ok(self.eq(d, g, phi, a, b, ty, rule, refs))
    }
}
