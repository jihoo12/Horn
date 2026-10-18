//! Untrusted producer for the semantic lemma calculus. Not a cubical elaborator.
use crate::cubical::engine::frontend::Producer;
use crate::sexp::{Sexp, atom, call};

pub fn univalence_demo() -> Producer {
    let mut p = Producer::default();
    let paths = atom("paths");
    let equivs = atom("equivs");
    let functions = atom("functions");
    let ua = atom("ua-map");
    let coe = atom("coe-map");
    let forget = atom("forget-map");
    let id_p = call("identity", [paths.clone()]);
    let id_e = call("identity", [equivs.clone()]);
    let ua_coe = call("then", [ua.clone(), coe.clone()]);
    let coe_ua = call("then", [coe.clone(), ua.clone()]);
    let beta_left = call("then", [ua_coe.clone(), forget.clone()]);
    let beta_right = call("then", [id_e.clone(), forget.clone()]);
    let m_ua = p.emit(
        "map.ua",
        vec![],
        call("mapping", [equivs.clone(), paths.clone(), ua.clone()]),
    );
    let m_coe = p.emit(
        "map.coe",
        vec![],
        call("mapping", [paths.clone(), equivs.clone(), coe.clone()]),
    );
    let m_forget = p.emit(
        "map.forget",
        vec![],
        call(
            "mapping",
            [equivs.clone(), functions.clone(), forget.clone()],
        ),
    );
    let m_id = p.emit(
        "map.identity",
        vec![],
        call("mapping", [equivs.clone(), equivs.clone(), id_e.clone()]),
    );
    let m_comp = p.emit(
        "map.then",
        vec![m_ua, m_coe],
        call("mapping", [equivs.clone(), equivs.clone(), ua_coe.clone()]),
    );
    let beta = p.emit(
        "hom.glue-beta",
        vec![],
        call(
            "hom",
            [
                equivs.clone(),
                functions.clone(),
                beta_left.clone(),
                forget.clone(),
            ],
        ),
    );
    let unit = p.emit(
        "hom.identity-left",
        vec![m_forget],
        call(
            "hom",
            [
                equivs.clone(),
                functions.clone(),
                beta_right.clone(),
                forget.clone(),
            ],
        ),
    );
    let sym = p.emit(
        "hom.sym",
        vec![unit],
        call(
            "hom",
            [
                equivs.clone(),
                functions.clone(),
                forget,
                beta_right.clone(),
            ],
        ),
    );
    let trans = p.emit(
        "hom.trans",
        vec![beta, sym],
        call("hom", [equivs.clone(), functions, beta_left, beta_right]),
    );
    let right = p.emit(
        "hom.equiv-ext",
        vec![m_comp, m_id, trans],
        call("hom", [equivs.clone(), equivs.clone(), ua_coe, id_e]),
    );
    p.result("equivalence-roundtrip", right);
    let left = p.emit(
        "hom.glue-eta",
        vec![],
        call("hom", [paths.clone(), paths.clone(), coe_ua, id_p]),
    );
    p.result("path-roundtrip", left);
    let iso = p.emit(
        "iso.intro",
        vec![m_coe, m_ua, left, right],
        call("iso", [paths.clone(), equivs.clone(), coe.clone(), ua]),
    );
    p.result("univalence-iso", iso);
    let eqv = p.emit(
        "equivalence.iso",
        vec![iso],
        call("equivalence", [paths, equivs, coe]),
    );
    p.result("univalence", eqv);
    p
}

/// Produce an Agda term for each step, INCLUDING its claimed type, so bugs in
/// this translator cannot silently select a theorem about a different map.
pub fn agda_replay(p: &Producer) -> Result<String, String> {
    fn term(s: &Sexp) -> Result<String, String> {
        match s {
            Sexp::Atom(a)
                if [
                    "paths",
                    "equivs",
                    "functions",
                    "ua-map",
                    "coe-map",
                    "forget-map",
                ]
                .contains(&a.as_str()) =>
            {
                Ok(a.clone())
            }
            Sexp::List(xs) if !xs.is_empty() => {
                let head = xs[0].atom()?;
                if !["identity", "then"].contains(&head) {
                    return Err(format!("unsupported map constructor: {head}"));
                }
                let args = xs[1..].iter().map(term).collect::<Result<Vec<_>, _>>()?;
                Ok(format!("({head} {})", args.join(" ")))
            }
            _ => Err(format!("unsupported syntax: {s}")),
        }
    }
    let mut out = String::from(
        "{-# OPTIONS --safe --cubical #-}\nmodule GeneratedUnivalence where\nopen import Cubical.Foundations.Prelude\nopen import Cubical.Foundations.Equiv using (_≃_)\nopen import UnivalenceCertificate\n\n",
    );
    for (i, (rule, refs, j)) in p.steps.iter().enumerate() {
        if refs.iter().any(|r| *r >= i) {
            return Err("replay requires earlier references".into());
        }
        let xs = j.list()?;
        let pred = xs[0].atom()?;
        let args = &xs[1..];
        let (ty, body) = match (pred, args) {
            ("mapping", [x, y, f]) => (format!("Map {} {}", term(x)?, term(y)?), term(f)?),
            ("hom", [x, y, f, g]) => {
                let ty = format!(
                    "Hom {{x = {}}} {{y = {}}} {} {}",
                    term(x)?,
                    term(y)?,
                    term(f)?,
                    term(g)?
                );
                let needed = match rule.as_str() {
                    "hom.refl" | "hom.identity-left" | "hom.identity-right" => 1,
                    "hom.sym" => 1,
                    "hom.trans" | "hom.then" => 2,
                    "hom.equiv-ext" => 3,
                    "hom.glue-beta" | "hom.glue-eta" => 0,
                    _ => return Err(format!("unknown hom rule: {rule}")),
                };
                if refs.len() != needed {
                    return Err("wrong premise count".into());
                }
                let r = |n: usize| format!("p{}", refs[n]);
                let body = match rule.as_str() {
                    "hom.refl" => "h-refl".into(),
                    "hom.identity-left" => "h-left".into(),
                    "hom.identity-right" => "h-right".into(),
                    "hom.sym" => format!("h-sym {}", r(0)),
                    "hom.trans" => format!("h-trans {} {}", r(0), r(1)),
                    "hom.then" => format!("h-then {} {}", r(0), r(1)),
                    "hom.equiv-ext" => format!("h-ext {}", r(2)),
                    "hom.glue-beta" => "h-beta".into(),
                    "hom.glue-eta" => "h-eta".into(),
                    _ => unreachable!(),
                };
                (ty, body)
            }
            ("iso", [x, y, f, g]) if rule == "iso.intro" && refs.len() == 4 => (
                format!(
                    "IsoProof {{x = {}}} {{y = {}}} {} {}",
                    term(x)?,
                    term(y)?,
                    term(f)?,
                    term(g)?
                ),
                format!("iso-intro p{} p{}", refs[2], refs[3]),
            ),
            ("equivalence", [x, y, f]) if rule == "equivalence.iso" && refs.len() == 1 => (
                format!(
                    "EquivProof {{x = {}}} {{y = {}}} {}",
                    term(x)?,
                    term(y)?,
                    term(f)?
                ),
                format!("equiv-iso p{}", refs[0]),
            ),
            _ => return Err(format!("unsupported judgment: {j}")),
        };
        out.push_str(&format!("p{i} : {ty}\np{i} = {body}\n\n"));
    }
    // The exported root is deliberately fixed to the requested canonical map.
    let root = p
        .steps
        .iter()
        .rposition(|(_, _, j)| {
            *j == call(
                "equivalence",
                [atom("paths"), atom("equivs"), atom("coe-map")],
            )
        })
        .ok_or("missing univalence root")?;
    out.push_str(&format!("checkedUnivalence : ∀ {{ℓ}} {{A B : Type ℓ}} → (A ≡ B) ≃ (A ≃ B)\ncheckedUnivalence {{A = A}} {{B = B}} = Semantics.exportUnivalence A B p{root}\n"));
    Ok(out)
}
