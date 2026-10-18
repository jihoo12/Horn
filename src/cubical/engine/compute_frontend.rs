//! Small computational regressions for Nat, dependent Sigma, and Path transport.
use crate::cubical::engine::face_frontend::Face;
use crate::cubical::engine::path_frontend::{cons, dim, papp, path, u, v};
use crate::cubical::engine::restricted_frontend::{RestrictedProducer, system};
use crate::cubical::engine::term::{Result, atom, call};

pub fn compute_core_demo() -> Result<RestrictedProducer> {
    let mut p = RestrictedProducer::default();
    p.enable_composition_computation();
    p.reuse_restricted_typings();
    p.reuse_certified_checks();
    let nil = atom("nil");
    let nat = atom("nat");
    let zero = atom("zero");
    let refl = call("plam", [zero.clone()]);
    let sigma = call("sigma", [nat.clone(), path(nat.clone(), v(0), v(0))]);
    let pair = call("pair", [zero.clone(), refl.clone()]);
    for (name, ty, base) in [
        ("nat-transport-zero", nat.clone(), zero.clone()),
        ("dependent-sigma-transport", sigma, pair),
        (
            "path-transport-refl",
            path(nat, zero.clone(), zero.clone()),
            refl,
        ),
    ] {
        let annotated = call("ann", [base.clone(), ty.clone()]);
        let t = call("comp", [ty.clone(), atom("ff"), zero.clone(), annotated]);
        let id = p.equality(0, &nil, &Face::True, &t, &base, &ty)?;
        p.f.path.p.result(name, id);
    }
    let function_type = call("pi", [atom("nat"), atom("nat")]);
    let function = call("ann", [call("lam", [atom("zero")]), function_type.clone()]);
    let source = call(
        "app",
        [
            call("comp", [function_type, atom("ff"), atom("zero"), function]),
            atom("zero"),
        ],
    );
    let id = p.equality(0, &nil, &Face::True, &source, &atom("zero"), &atom("nat"))?;
    p.f.path.p.result("pi-transport-zero-application", id);
    let dependent_function_type = call("pi", [atom("nat"), path(atom("nat"), v(0), v(0))]);
    let dependent_function = call(
        "ann",
        [
            call("lam", [call("plam", [v(0)])]),
            dependent_function_type.clone(),
        ],
    );
    let source = call(
        "app",
        [
            call(
                "comp",
                [
                    dependent_function_type,
                    atom("ff"),
                    atom("zero"),
                    dependent_function,
                ],
            ),
            atom("zero"),
        ],
    );
    let result_type = path(atom("nat"), atom("zero"), atom("zero"));
    let id = p.equality(
        0,
        &nil,
        &Face::True,
        &source,
        &call("plam", [atom("zero")]),
        &result_type,
    )?;
    p.f.path.p.result("dependent-product-transport-refl", id);
    // Nonconstant dependent Sigma family over P : Path U A B.
    let gab = cons(u(0), cons(u(0), nil.clone()));
    let gp = cons(path(u(0), v(1), v(0)), gab);
    let initial = call("sigma", [v(2), path(v(3), v(0), v(0))]);
    let g = cons(initial, gp);
    let a = papp(v(1), dim(0));
    let family = call("sigma", [a.clone(), path(papp(v(2), dim(1)), v(0), v(0))]);
    let fill = call(
        "comp",
        [
            papp(v(1), call("meet", [dim(1), dim(0)])),
            call("for", [atom("ff"), Face::End(0, false).quote()]),
            system(&[
                (Face::False, call("fst", [atom("zero")])),
                (Face::End(1, false), call("fst", [v(0)])),
            ]),
            call("fst", [v(0)]),
        ],
    );
    let rhs = call(
        "pair",
        [
            call(
                "comp",
                [
                    a,
                    atom("ff"),
                    call("fst", [atom("zero")]),
                    call("fst", [v(0)]),
                ],
            ),
            call(
                "comp",
                [
                    path(papp(v(1), dim(1)), fill.clone(), fill),
                    atom("ff"),
                    call("snd", [atom("zero")]),
                    call("snd", [v(0)]),
                ],
            ),
        ],
    );
    let source = call("comp", [family, atom("ff"), atom("zero"), v(0)]);
    let out = call("sigma", [v(2), path(v(3), v(0), v(0))]);
    let id = p.equality(0, &g, &Face::True, &source, &rhs, &out)?;
    p.f.path
        .p
        .result("nonconstant-dependent-sigma-computation", id);
    // Contravariant argument filling for a nonconstant product family.
    let gab = cons(u(0), cons(u(0), nil.clone()));
    let gp = cons(path(u(0), v(1), v(0)), gab);
    let gy = cons(v(1), gp); // y:B, P, B, A
    let product = call("pi", [papp(v(1), dim(0)), papp(v(2), dim(0))]);
    let identity = call("ann", [call("lam", [v(0)]), call("pi", [v(3), v(4)])]);
    let source = call(
        "app",
        [
            call(
                "comp",
                [product, atom("ff"), atom("zero"), identity.clone()],
            ),
            v(0),
        ],
    );
    let reverse_fill = call(
        "comp",
        [
            papp(
                v(1),
                call("neg", [call("meet", [call("neg", [dim(1)]), dim(0)])]),
            ),
            call("for", [atom("ff"), Face::End(0, true).quote()]),
            system(&[(Face::False, atom("zero")), (Face::End(1, true), v(0))]),
            v(0),
        ],
    );
    let v0 =
        p.f.path
            .transform(
                &reverse_fill,
                &crate::cubical::engine::path_frontend::Op::DSubst(0, atom("i0")),
            )?
            .0;
    let rhs = call(
        "comp",
        [
            papp(v(1), dim(0)),
            atom("ff"),
            call("app", [atom("zero"), reverse_fill]),
            call("app", [identity, v0]),
        ],
    );
    let id = p.equality(0, &gy, &Face::True, &source, &rhs, &v(2))?;
    p.f.path
        .p
        .result("nonconstant-product-contravariant-computation", id);
    // A path family depending on BOTH composition and path dimensions.
    let gp = cons(path(u(0), atom("nat"), atom("nat")), nil);
    let gq = cons(path(path(u(0), atom("nat"), atom("nat")), v(0), v(0)), gp);
    let gb = cons(path(papp(v(1), dim(0)), atom("zero"), atom("zero")), gq);
    let family = path(papp(papp(v(1), dim(1)), dim(0)), atom("zero"), atom("zero"));
    let source = call("comp", [family, atom("ff"), atom("zero"), v(0)]);
    let tube = system(&[
        (Face::False, papp(atom("zero"), dim(1))),
        (Face::End(1, false), atom("zero")),
        (Face::End(1, true), atom("zero")),
    ]);
    let rhs = call(
        "plam",
        [call(
            "comp",
            [
                papp(papp(v(1), dim(0)), dim(1)),
                call(
                    "for",
                    [
                        atom("ff"),
                        call(
                            "for",
                            [Face::End(0, false).quote(), Face::End(0, true).quote()],
                        ),
                    ],
                ),
                tube,
                papp(v(0), dim(0)),
            ],
        )],
    );
    let out = path(papp(v(2), dim(0)), atom("zero"), atom("zero"));
    let id = p.equality(0, &gb, &Face::True, &source, &rhs, &out)?;
    p.f.path.p.result("mixed-dimension-path-computation", id);
    Ok(p)
}
pub fn compute_demo() -> Result<RestrictedProducer> {
    let mut p = compute_core_demo()?;
    let (program, _) = p.canonical_program(&crate::cubical::engine::frontend::number(0))?;
    for (name, d, extent, tube) in [
        ("empty-universe-composition", 0, Face::False, atom("zero")),
        (
            "partial-universe-composition",
            1,
            Face::End(0, false),
            atom("nat"),
        ),
    ] {
        let source = call("comp", [u(0), extent.quote(), tube.clone(), atom("nat")]);
        let line = call(
            "ann",
            [
                call("plam", [tube.clone()]),
                path(u(0), tube.clone(), atom("nat")),
            ],
        );
        let e = [tube.clone(), atom("nat"), line]
            .into_iter()
            .fold(program.clone(), |t, a| call("app", [t, a]));
        let rhs = call("glue-type", [atom("nat"), extent.quote(), tube, e]);
        let id = p.equality(d, &atom("nil"), &Face::True, &source, &rhs, &u(0))?;
        p.f.path.p.result(name, id);
    }
    let (program1, _) = p.canonical_program(&crate::cubical::engine::frontend::number(1))?;
    let extent1 = Face::End(0, false);
    let source1 = call("comp", [u(1), extent1.quote(), u(0), u(0)]);
    let line1 = call("ann", [call("plam", [u(0)]), path(u(1), u(0), u(0))]);
    let e1 = [u(0), u(0), line1]
        .into_iter()
        .fold(program1, |t, a| call("app", [t, a]));
    let rhs1 = call("glue-type", [u(0), extent1.quote(), u(0), e1]);
    let id = p.equality(1, &atom("nil"), &Face::True, &source1, &rhs1, &u(1))?;
    p.f.path.p.result("next-level-universe-composition", id);
    let gab = cons(u(0), cons(u(0), atom("nil")));
    let gp = cons(path(u(0), v(1), v(0)), gab);
    let extent = Face::End(0, false);
    let source = call("comp", [u(0), extent.quote(), papp(v(0), dim(0)), v(2)]);
    let endpoint = papp(v(0), atom("i1"));
    let line = call(
        "ann",
        [
            call("plam", [papp(v(0), call("neg", [dim(0)]))]),
            path(u(0), endpoint.clone(), v(2)),
        ],
    );
    let e = [endpoint.clone(), v(2), line]
        .into_iter()
        .fold(program, |t, a| call("app", [t, a]));
    let rhs = call("glue-type", [v(2), extent.quote(), endpoint, e]);
    let id = p.equality(1, &gp, &Face::True, &source, &rhs, &u(0))?;
    p.f.path.p.result("nonconstant-universe-composition", id);
    Ok(p)
}
