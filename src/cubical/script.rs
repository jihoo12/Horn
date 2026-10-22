//! Cubical scripts: definitions, typing checks and evaluation, elaborated to
//! the core syntax and certified by the engine. Every `def`, `check` and
//! `eval` becomes a fixed goal; the whole derivation is encoded as an oracle
//! and checked by the kernel before any result is reported.
//!
//! ```text
//! (def not (pi b bool bool) (lam b bool (bif c bool bfalse btrue b)))
//! (eval r (app not btrue))                       ; r = bfalse : bool
//! ```
//!
//! `(data NAME (CTOR ARG-TYPE...) ...)` declares a closed data type; its
//! rules are generated and appended to the theory the certificate is checked
//! against. Constructors apply like functions, `(elim NAME k P (METHODS...) x)`
//! eliminates into the motive P over `k : NAME`.
//!
//! Terms use named binders. `(lam x A body)`, `(pi x A B)`, `(sigma x A B)`,
//! `(plam i body)`, `(path i A l r)` or `(path A l r)`, `(papp p r)`,
//! `(bif c P t f b)` (P is the motive over `c : bool`), `(suc n)`,
//! `(natrec k P z s n)` (motive P over `k : nat`, `s : Π k. P k → P (suc k)`),
//! numerals, `(pair a b)`,
//! `(fst p)`, `(snd p)`, `(app f a ...)`, `(ann t A)`, `(u N)`, `(equiv A B)`
//! and `(transport i A x)` (transport of x along the line `i ↦ A`).
//! Constants are `bool btrue bfalse nat zero`. The prelude names `ua`
//! (`Π A B : U0. Equiv A B → Path U0 A B`) and `iso-equiv`
//! (`Π X Y f g s t. isEquiv f`) are closed library terms, checked like any
//! definition; neither is an axiom. Definitions are closed and transparent.
use super::display::{Printer, Scope};
use super::engine::data::{self, ArgTy, Ctor, Data};
use super::engine::deep_univalence_frontend;
use super::engine::face_frontend::Face;
use super::engine::iso_equiv_frontend::{iso_equiv_term, iso_equiv_type};
use super::engine::path_frontend::{dim, papp, path, v};
use super::engine::restricted_frontend::RestrictedProducer;
use super::engine::term::{Result, Sexp, atom, call, parse};
use super::engine::ua_frontend::{ua_term, ua_type};
use super::generate::{Certificate, Regenerated, certify};
use std::collections::HashMap;

const FUEL: usize = 100_000;

/// The universe level a def-poly with holes is checked at, standing for its
/// level variable when its goals are shown.
const LEVEL_MARK: usize = 64;

/// One reported evaluation: `name = value : type`.
pub struct Evaluation {
    pub name: String,
    pub value: String,
    pub ty: String,
}

pub struct Script {
    pub certified: Regenerated,
    pub evaluations: Vec<Evaluation>,
    /// One schematic certificate per level-polymorphic definition.
    pub polymorphic: Vec<Polymorphic>,
}

/// `∀L. ⊢ NAME : TYPE`, as a schematic certificate accepted by
/// `schematic::check`, generalized from the definition's proof at level 0.
pub struct Polymorphic {
    pub name: String,
    pub goals: String,
    pub proof: String,
    pub steps: usize,
    pub inductions: usize,
}

#[derive(Clone, Default)]
struct Names {
    ordinary: Vec<String>,
    dimensions: Vec<String>,
    /// Level variables and the unary level terms they stand for.
    levels: Vec<(String, Sexp)>,
}

impl Names {
    fn with_ordinary(&self, name: &str) -> Self {
        let mut out = self.clone();
        out.ordinary.push(name.to_owned());
        out
    }
    fn with_dimension(&self, name: &str) -> Self {
        let mut out = self.clone();
        out.dimensions.push(name.to_owned());
        out
    }
}

/// A face under one more dimension binder: every dimension index rises.
fn shift_face(f: &Face) -> Face {
    match f {
        Face::False | Face::True => f.clone(),
        Face::End(n, b) => Face::End(n + 1, *b),
        Face::And(a, b) => shift_face(a).and(shift_face(b)),
        Face::Or(a, b) => shift_face(a).or(shift_face(b)),
    }
}

fn index(names: &[String], name: &str) -> Option<usize> {
    names.iter().rev().position(|n| n == name)
}

fn level(s: &Sexp) -> Result<usize> {
    let text = s.atom()?;
    match text.parse::<usize>() {
        Ok(n) if n <= 8 && text.bytes().all(|c| c.is_ascii_digit()) => Ok(n),
        _ => Err(format!("expected a universe level 0..8, found {text}")),
    }
}

fn binder(s: &Sexp) -> Result<&str> {
    let name = s.atom()?;
    let ok = name
        .chars()
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '\''));
    if !ok || RESERVED.contains(&name) {
        return Err(format!("invalid binder name {name}"));
    }
    Ok(name)
}

const RESERVED: &[&str] = &[
    "bool",
    "btrue",
    "bfalse",
    "nat",
    "zero",
    "i0",
    "i1",
    "u",
    "pi",
    "lam",
    "app",
    "sigma",
    "pair",
    "fst",
    "snd",
    "path",
    "plam",
    "papp",
    "bif",
    "ann",
    "equiv",
    "transport",
    "neg",
    "meet",
    "join",
    "ua",
    "iso-equiv",
    "suc",
    "natrec",
    "data",
    "elim",
    "ua-at",
    "iso-equiv-at",
    "at",
    "def-poly",
    "univalence-at",
    "s1",
    "base",
    "loop",
    "s1rec",
    "hcomp",
    "comp",
    "and",
    "or",
];

struct Elaborator {
    p: RestrictedProducer,
    /// Holes written in the current form, in source order: their display
    /// name, and the names in scope where they were elaborated (`None` for
    /// a hole in a position the elaborator skips, such as a lambda's
    /// domain).
    holes: Vec<(String, Option<Names>)>,
    /// While a def-poly with holes is checked at a marker level: that level
    /// and the level variable it stands for.
    level_marker: Option<(usize, String)>,
    defs: HashMap<String, Sexp>,
    /// Level-polymorphic definitions: level parameter, type, term (source).
    poly: HashMap<String, (String, Sexp, Sexp)>,
    prelude: HashMap<&'static str, Sexp>,
}

fn producer() -> RestrictedProducer {
    let mut p = RestrictedProducer::default();
    p.f.path.p.archive_judgments();
    p.reuse_restricted_typings();
    p.f.path.memoize_transformations();
    p.f.path.use_scoped_identities();
    p.reuse_certified_checks();
    p.strengthen_typings();
    p.keep_reduct_types();
    p.enable_composition_computation();
    p.closed_term_reuse = true;
    p
}

/// Generalize the derivation `id` of `t0 : ty0` (the level-0 instance, in
/// the script's producer) over universe levels, check the schematic
/// certificate, and require its goal to be exactly `expected`, the user's
/// statement with level `L`. Only the steps `id` depends on are generalized.
fn generalize_definition(
    name: &str,
    steps: &crate::cubical::engine::frontend::Producer,
    id: usize,
    expected: &Sexp,
    theory: &str,
) -> Result<Polymorphic> {
    let goals = format!("(goal {name} {})\n", steps.judgment(id));
    let mut proof = Vec::new();
    steps
        .write_reachable_of(&[(name.to_owned(), id)], &mut proof)
        .map_err(|e| e.to_string())?;
    let (mut sg, mut sp) = (Vec::new(), Vec::new());
    crate::generalize::generalize(
        theory,
        &goals,
        &proof[..],
        &["max:2"],
        Some("u:0"),
        Some((&mut sg, &mut sp)),
    )?;
    let (sg, sp) = (
        String::from_utf8(sg).map_err(|e| e.to_string())?,
        String::from_utf8(sp).map_err(|e| e.to_string())?,
    );
    let report = crate::schematic::check(theory, &sg, sp.as_bytes())?;
    let want = format!("(goal {name} {expected})");
    if !sg.lines().any(|l| l == want) {
        let got = sg.lines().find(|l| l.starts_with("(goal ")).unwrap_or("");
        let at = got
            .bytes()
            .zip(want.bytes())
            .take_while(|(a, b)| a == b)
            .count();
        let near = |s: &str| {
            s.get(at.saturating_sub(60)..(at + 60).min(s.len()))
                .unwrap_or("")
                .to_owned()
        };
        return Err(format!(
            "the proof does not generalize to the stated level: at byte {at}, got ...{}... but stated ...{}...",
            near(got),
            near(&want)
        ));
    }
    Ok(Polymorphic {
        name: name.to_owned(),
        goals: sg,
        proof: sp,
        steps: report.steps,
        inductions: report.inductions,
    })
}

impl Elaborator {
    fn new() -> Result<Self> {
        let mut p = producer();
        let mut prelude = HashMap::new();
        prelude.insert("ua", call("ann", [ua_term(), ua_type(&mut p, 0)?]));
        prelude.insert(
            "iso-equiv",
            call(
                "ann",
                [iso_equiv_term(&mut p, 0, 0)?, iso_equiv_type(&mut p, 0, 0)?],
            ),
        );
        Ok(Self {
            p,
            holes: Vec::new(),
            level_marker: None,
            defs: HashMap::new(),
            poly: HashMap::new(),
            prelude,
        })
    }

    /// A level: a numeral, a level variable, or `(s LEVEL)`.
    fn level_term(&self, s: &Sexp, names: &Names) -> Result<Sexp> {
        match s {
            Sexp::Atom(a) => {
                if let Some((_, t)) = names.levels.iter().rev().find(|(n, _)| **n == **a) {
                    return Ok(t.clone());
                }
                let n = level(s)?;
                Ok(super::engine::term::numeral(n))
            }
            Sexp::List(xs) if xs.len() == 2 && xs[0] == atom("s") => {
                Ok(call("s", [self.level_term(&xs[1], names)?]))
            }
            _ => Err(format!("invalid level {s}")),
        }
    }

    /// A level-polymorphic definition's term and type at `level`.
    fn instance(&mut self, param: &str, level: Sexp, ty: &Sexp, t: &Sexp) -> Result<(Sexp, Sexp)> {
        let names = Names {
            levels: vec![(param.to_owned(), level)],
            ..Names::default()
        };
        Ok((self.term(t, &names)?, self.term(ty, &names)?))
    }

    fn interval(&self, s: &Sexp, names: &Names) -> Result<Sexp> {
        match s {
            Sexp::Atom(a) if &**a == "i0" || &**a == "i1" => Ok(s.clone()),
            Sexp::Atom(a) => index(&names.dimensions, a)
                .map(dim)
                .ok_or_else(|| format!("unknown dimension {a}")),
            Sexp::List(xs) => match (xs.first().map(Sexp::atom).transpose()?, &xs[1..]) {
                (Some("neg"), [r]) => Ok(call("neg", [self.interval(r, names)?])),
                (Some(op @ ("meet" | "join")), [r, s]) => Ok(call(
                    op,
                    [self.interval(r, names)?, self.interval(s, names)?],
                )),
                _ => Err(format!("invalid interval {s}")),
            },
        }
    }

    /// A face: `(= i 0)`, `(= i 1)`, `(and F G)`, `(or F G)`, `ff` or `ft`.
    fn face(&self, s: &Sexp, names: &Names) -> Result<Face> {
        let bad = || format!("invalid face {s}");
        Ok(match s {
            Sexp::Atom(a) if &**a == "ff" => Face::False,
            Sexp::Atom(a) if &**a == "ft" => Face::True,
            Sexp::Atom(_) => return Err(bad()),
            Sexp::List(xs) => match (xs.first().map(Sexp::atom).transpose()?, &xs[1..]) {
                (Some("="), [i, end]) => {
                    let name = i.atom()?;
                    let k = index(&names.dimensions, name)
                        .ok_or_else(|| format!("unknown dimension {name}"))?;
                    match end.atom()? {
                        "0" => Face::End(k, false),
                        "1" => Face::End(k, true),
                        _ => return Err(bad()),
                    }
                }
                (Some("and"), [a, b]) => self.face(a, names)?.and(self.face(b, names)?),
                (Some("or"), [a, b]) => self.face(a, names)?.or(self.face(b, names)?),
                _ => return Err(bad()),
            },
        })
    }

    /// `(comp j A ((FACE TERM) ...) BASE)`: composition along the line
    /// `j ↦ A` of BASE with a system whose branches bind `j`; its face is
    /// the disjunction of the branch faces. `hcomp` is the same in a type
    /// that does not depend on `j`, written outside `j`'s scope.
    fn composition(
        &mut self,
        homogeneous: bool,
        j: &Sexp,
        a: &Sexp,
        sides: &Sexp,
        base: &Sexp,
        names: &Names,
    ) -> Result<Sexp> {
        let inner = names.with_dimension(binder(j)?);
        // A homogeneous type and the branch faces are written outside j's
        // scope: they are elaborated there and then shifted under j, so a
        // binder j that shadows an outer dimension does not capture them.
        let family = if homogeneous {
            let outer = self.term(a, names)?;
            self.p
                .f
                .path
                .transform(&outer, &super::engine::path_frontend::Op::DShift(0))?
                .0
        } else {
            self.term(a, &inner)?
        };
        let Sexp::List(sides) = sides else {
            return Err("a composition needs a list of (FACE TERM) branches".into());
        };
        let mut extent = Face::False;
        let mut system = atom("snil");
        for side in sides.iter().rev() {
            let Sexp::List(pair) = side else {
                return Err(format!("invalid branch {side}"));
            };
            let [phi, t] = &pair[..] else {
                return Err(format!("a branch is (FACE TERM): {side}"));
            };
            let outer = self.face(phi, names)?;
            let shifted = shift_face(&outer);
            let t = self.term(t, &inner)?;
            system = call("side", [shifted.quote(), t, system]);
            extent = if extent == Face::False {
                outer
            } else {
                outer.or(extent)
            };
        }
        Ok(call(
            "comp",
            [
                family,
                extent.quote(),
                call("system", [system]),
                self.term(base, names)?,
            ],
        ))
    }

    /// A hole `?` or `(? NAME)`: the core term `(hole K)`, which never has
    /// a derivation; checking it records what it must be.
    fn new_hole(&mut self, k: &Sexp, names: &Names) -> Result<Sexp> {
        let index: usize = k.atom()?.parse().map_err(|_| "invalid hole")?;
        let (_, scope) = self.holes.get_mut(index).ok_or("invalid hole")?;
        // A def-poly elaborates its source twice; the first scope stands.
        scope.get_or_insert_with(|| names.clone());
        Ok(call("hole", [k.clone()]))
    }

    /// The error for a form that failed. If the checker met holes, show
    /// what each must be instead of the search failure they caused.
    fn explain(&self, what: &str, err: String) -> String {
        fn context_length(g: &Sexp) -> usize {
            let mut n = 0;
            let mut tail = g;
            while let Sexp::List(xs) = tail
                && xs.len() == 3
            {
                n += 1;
                tail = &xs[2];
            }
            n
        }
        if self.p.holes.is_empty() && self.holes.is_empty() {
            return format!("{what}: {err}");
        }
        let mut known = HashMap::new();
        for (name, t) in &self.defs {
            known.insert(t.clone(), name.clone());
        }
        for (name, t) in &self.prelude {
            known.insert(t.clone(), (*name).to_owned());
        }
        let hole_names: Vec<String> = self.holes.iter().map(|(n, _)| n.clone()).collect();
        let printer = Printer {
            known: &known,
            holes: &hole_names,
            level: self
                .level_marker
                .as_ref()
                .map(|(mark, var)| (*mark, var.as_str())),
        };
        // One goal per hole: where it was checked in the context it was
        // written in, if it was; otherwise where it was first met.
        let mut shown_holes: Vec<&crate::cubical::engine::restricted_frontend::Hole> = Vec::new();
        for hole in &self.p.holes {
            let k: usize = hole
                .id
                .atom()
                .ok()
                .and_then(|a| a.parse().ok())
                .unwrap_or(0);
            let fits = |h: &crate::cubical::engine::restricted_frontend::Hole| {
                self.holes.get(k).is_some_and(|(_, names)| {
                    names.as_ref().is_some_and(|names| {
                        names.dimensions.len() == h.dimensions
                            && names.ordinary.len() == context_length(&h.context)
                    })
                })
            };
            match shown_holes.iter().position(|h| h.id == hole.id) {
                Some(i) if !fits(shown_holes[i]) && fits(hole) => shown_holes[i] = hole,
                Some(_) => {}
                None => shown_holes.push(hole),
            }
        }
        // Every hole written, in order; those the checker never reached (it
        // stopped before them, or never checks that position) have no goal.
        let hole_number = |h: &crate::cubical::engine::restricted_frontend::Hole| -> usize {
            h.id.atom().ok().and_then(|a| a.parse().ok()).unwrap_or(0)
        };
        let order: Vec<(
            usize,
            Option<&crate::cubical::engine::restricted_frontend::Hole>,
        )> = (0..self.holes.len().max(shown_holes.len()))
            .map(|k| (k, shown_holes.iter().copied().find(|h| hole_number(h) == k)))
            .collect();
        let count = order.len();
        let mut out = format!(
            "{what}: {count} goal{} to fill",
            if count == 1 { "" } else { "s" }
        );
        for (k, hole) in order {
            let Some(hole) = hole else {
                let (shown, scope) = &self.holes[k];
                let why = if scope.is_some() {
                    "not reached by the checker, so it has no goal yet; fill the others first"
                } else {
                    "in a position that is not checked, such as a lambda's domain; write it out"
                };
                out.push_str(&format!("\n\n{shown}\n  ({why})"));
                continue;
            };
            let (shown, names) = match self.holes.get(k) {
                Some((shown, names)) => (shown.clone(), names.clone().unwrap_or_default()),
                None => (format!("?{k}"), Names::default()),
            };
            out.push_str(&format!("\n\n{shown}"));
            // Context entries, outermost first; each type is in the scope of
            // the entries before it.
            let mut entries = Vec::new();
            let mut tail = &hole.context;
            while let Sexp::List(xs) = tail
                && xs.len() == 3
            {
                entries.push(xs[1].clone());
                tail = &xs[2];
            }
            entries.reverse();
            let mut vars: Vec<String> = if names.ordinary.len() == entries.len() {
                names.ordinary.clone()
            } else {
                (0..entries.len()).map(|i| format!("x{i}")).collect()
            };
            // A variable shadowed by a later one of the same name is shown
            // as `x✝`; it cannot be referred to here.
            for i in 0..vars.len() {
                if vars[i + 1..].contains(&vars[i]) {
                    vars[i].push('✝');
                }
            }
            let mut dims: Vec<String> = if names.dimensions.len() == hole.dimensions {
                names.dimensions.clone()
            } else {
                (0..hole.dimensions).map(|i| format!("i{i}")).collect()
            };
            for i in 0..dims.len() {
                if dims[i + 1..].contains(&dims[i]) {
                    dims[i].push('✝');
                }
            }
            for (i, ty) in entries.iter().enumerate() {
                let scope = Scope {
                    vars: vars[..i].to_vec(),
                    dims: dims.clone(),
                };
                out.push_str(&format!("\n  {} : {}", vars[i], printer.term(ty, &scope)));
            }
            if !dims.is_empty() {
                out.push_str(&format!("\n  {} : I", dims.join(" ")));
            }
            let scope = Scope {
                vars: vars.clone(),
                dims: dims.clone(),
            };
            if hole.face != Face::True {
                out.push_str(&format!("\n  under {}", printer.face(&hole.face, &scope)));
            }
            match &hole.ty {
                Some(ty) if hole.not_a_type && hole.boundary.is_some() => out.push_str(&format!(
                    "\n  ⊢ {}  (but the path type it is in is not a type, so nothing can fill this)",
                    printer.term(ty, &scope)
                )),
                Some(ty) if hole.not_a_type => out.push_str(&format!(
                    "\n  ⊢ {}  (not a type, so nothing can fill this)",
                    printer.term(ty, &scope)
                )),
                Some(ty) => out.push_str(&format!("\n  ⊢ {}", printer.term(ty, &scope))),
                None => out
                    .push_str("\n  ⊢ (its type is not known here; annotate it with (ann ? TYPE))"),
            }
            if let Some((left, right)) = &hole.boundary {
                let outer = Scope {
                    vars: vars.clone(),
                    dims: dims[..dims.len().saturating_sub(1)].to_vec(),
                };
                let i = dims.last().cloned().unwrap_or_default();
                out.push_str(&format!(
                    "\n  where {i} = 0 must give {}\n        {i} = 1 must give {}",
                    printer.term(left, &outer),
                    printer.term(right, &outer)
                ));
            }
        }
        // Equations between terms with holes, which the goals' types alone
        // do not express. Their variables are named as in a goal with the
        // same context, if there is one.
        if !self.p.constraints.is_empty() {
            out.push_str("\n\nand these must hold:");
        }
        for c in &self.p.constraints {
            let named = self.p.holes.iter().find_map(|h| {
                let k: usize = h.id.atom().ok()?.parse().ok()?;
                let names = self.holes.get(k)?.1.clone()?;
                (h.context == c.context
                    && h.dimensions == c.dimensions
                    && names.ordinary.len() == context_length(&c.context)
                    && names.dimensions.len() == c.dimensions)
                    .then_some(names)
            });
            let scope = match named {
                Some(names) => Scope {
                    vars: names.ordinary,
                    dims: names.dimensions,
                },
                None => Scope {
                    vars: (0..context_length(&c.context))
                        .map(|i| format!("x{i}"))
                        .collect(),
                    dims: (0..c.dimensions).map(|i| format!("i{i}")).collect(),
                },
            };
            out.push_str(&format!(
                "\n  {} = {} : {}",
                printer.term(&c.left, &scope),
                printer.term(&c.right, &scope),
                printer.term(&c.ty, &scope)
            ));
            if c.face != Face::True {
                out.push_str(&format!("  under {}", printer.face(&c.face, &scope)));
            }
        }
        out
    }

    fn term(&mut self, s: &Sexp, names: &Names) -> Result<Sexp> {
        let xs = match s {
            Sexp::Atom(a) => {
                return if ["bool", "btrue", "bfalse", "nat", "zero", "s1", "base"].contains(&&**a) {
                    Ok(s.clone())
                } else if let Ok(n) = a.parse::<usize>()
                    && a.bytes().all(|c| c.is_ascii_digit())
                {
                    if n > 10_000 {
                        return Err(format!("numeral {n} is too large"));
                    }
                    Ok((0..n).fold(atom("zero"), |t, _| call("suc", [t])))
                } else if let Some(i) = index(&names.ordinary, a) {
                    Ok(v(i))
                } else if let Some(d) = data::by_name(a) {
                    if d.params == 0 {
                        Ok(atom(&d.ty))
                    } else {
                        Err(format!("{a} needs {} type parameters", d.params))
                    }
                } else if let Some((d, i)) = data::by_ctor_name(a) {
                    let c = &d.ctors[i];
                    if c.arity() == 0 {
                        Ok(atom(&c.symbol))
                    } else {
                        Err(format!("constructor {a} needs {} arguments", c.args.len()))
                    }
                } else if let Some(t) = self.defs.get(&**a) {
                    Ok(t.clone())
                } else if let Some(t) = self.prelude.get(&**a) {
                    Ok(t.clone())
                } else {
                    Err(format!("unknown name {a}"))
                };
            }
            Sexp::List(xs) => xs,
        };
        let head = xs.first().ok_or("empty term")?.atom()?;
        let args = &xs[1..];
        Ok(match (head, args) {
            ("?#", [k]) => self.new_hole(k, names)?,
            ("u", [l]) => call("u", [self.level_term(l, names)?]),
            ("at", [name, l]) => {
                let name = name.atom()?;
                let (param, ty, t) = self
                    .poly
                    .get(name)
                    .cloned()
                    .ok_or_else(|| format!("{name} is not level-polymorphic"))?;
                let level = self.level_term(l, names)?;
                let (t, ty) = self.instance(&param, level, &ty, &t)?;
                call("ann", [t, ty])
            }
            (former @ ("pi" | "sigma"), [x, a, b]) => {
                let a = self.term(a, names)?;
                let b = self.term(b, &names.with_ordinary(binder(x)?))?;
                call(former, [a, b])
            }
            ("lam", [x, _domain, body]) => {
                // The domain is checked where the lambda meets its expected
                // type; the core lambda carries no annotation.
                call("lam", [self.term(body, &names.with_ordinary(binder(x)?))?])
            }
            ("app", [f, rest @ ..]) if !rest.is_empty() => {
                let mut out = self.term(f, names)?;
                for a in rest {
                    out = call("app", [out, self.term(a, names)?]);
                }
                out
            }
            ("pair", [a, b]) => call("pair", [self.term(a, names)?, self.term(b, names)?]),
            (proj @ ("fst" | "snd"), [t]) => call(proj, [self.term(t, names)?]),
            ("plam", [i, body]) => call(
                "plam",
                [self.term(body, &names.with_dimension(binder(i)?))?],
            ),
            ("path", [i, a, l, r]) => path(
                self.term(a, &names.with_dimension(binder(i)?))?,
                self.term(l, names)?,
                self.term(r, names)?,
            ),
            ("path", [a, l, r]) => path(
                self.term(a, &names.with_dimension("_"))?,
                self.term(l, names)?,
                self.term(r, names)?,
            ),
            ("papp", [p, r]) => papp(self.term(p, names)?, self.interval(r, names)?),
            ("suc", [n]) => call("suc", [self.term(n, names)?]),
            ("loop", [r]) => call("loop", [self.interval(r, names)?]),
            ("s1rec", [a, b, l, x]) => call(
                "s1rec",
                [
                    self.term(a, names)?,
                    self.term(b, names)?,
                    self.term(l, names)?,
                    self.term(x, names)?,
                ],
            ),
            (head @ ("bif" | "natrec"), [c, motive, t, f, b]) => call(
                head,
                [
                    self.term(motive, &names.with_ordinary(binder(c)?))?,
                    self.term(t, names)?,
                    self.term(f, names)?,
                    self.term(b, names)?,
                ],
            ),
            ("ann", [t, a]) => call("ann", [self.term(t, names)?, self.term(a, names)?]),
            // The prelude at other universe levels; each instance is a
            // closed term whose typing is checked where it is used.
            // Built at level 0, where every universe is the parameter's,
            // then moved to the requested level, which may be a variable.
            ("ua-at", [l]) => {
                let level = self.level_term(l, names)?;
                let ty = ua_type(&mut self.p, 0)?;
                relevel(&call("ann", [ua_term(), ty]), &level)
            }
            ("univalence-at", [l]) => {
                let level = self.level_term(l, names)?;
                let t = deep_univalence_frontend::univalence_term(&mut self.p)?;
                let ty = deep_univalence_frontend::univalence_type(&mut self.p)?;
                relevel(&call("ann", [t, ty]), &level)
            }
            ("iso-equiv-at", [l]) => {
                let level = self.level_term(l, names)?;
                let t = iso_equiv_term(&mut self.p, 0, 0)?;
                let ty = iso_equiv_type(&mut self.p, 0, 0)?;
                relevel(&call("ann", [t, ty]), &level)
            }
            ("elim", [ty, rest @ ..]) => {
                let d =
                    data::by_name(ty.atom()?).ok_or_else(|| format!("unknown data type {ty}"))?;
                // `(elim T k P (METHODS) x)`, or with parameters
                // `(elim T (PARAMS) k P (METHODS) x)`.
                let (params, k, motive, methods, x) = match rest {
                    [k, motive, methods, x] if d.params == 0 => (&[][..], k, motive, methods, x),
                    [params, k, motive, methods, x] => (params.list()?, k, motive, methods, x),
                    _ => return Err(format!("invalid elim {s}")),
                };
                if params.len() != d.params {
                    return Err(format!("elim {} needs {} parameters", d.name, d.params));
                }
                let methods = methods.list()?;
                if methods.len() != d.ctors.len() {
                    return Err(format!("elim {} needs {} methods", d.name, d.ctors.len()));
                }
                let mut items = Vec::new();
                for a in params {
                    items.push(self.term(a, names)?);
                }
                items.push(self.term(motive, &names.with_ordinary(binder(k)?))?);
                for m in methods {
                    items.push(self.term(m, names)?);
                }
                items.push(self.term(x, names)?);
                call(&d.elim, items)
            }
            (c, args) if data::by_ctor_name(c).is_some() => {
                // Parameters are not written: `(cons btrue nil)`. They come
                // from the fields or from the expected type.
                let (d, i) = data::by_ctor_name(c).unwrap();
                let ctor = &d.ctors[i];
                if args.len() != ctor.arity() {
                    return Err(format!("constructor {c} needs {} arguments", ctor.arity()));
                }
                let n = ctor.args.len();
                let mut out = args[..n]
                    .iter()
                    .map(|a| self.term(a, names))
                    .collect::<Result<Vec<_>>>()?;
                if ctor.boundary.is_some() {
                    out.push(self.interval(&args[n], names)?);
                }
                data::apply(&ctor.symbol, out)
            }
            (n, args) if data::by_name(n).is_some() => {
                let d = data::by_name(n).unwrap();
                if args.len() != d.params {
                    return Err(format!("{n} needs {} type parameters", d.params));
                }
                let args = args
                    .iter()
                    .map(|a| self.term(a, names))
                    .collect::<Result<Vec<_>>>()?;
                data::apply(&d.ty, args)
            }
            ("equiv", [a, b]) => {
                let (a, b) = (self.term(a, names)?, self.term(b, names)?);
                self.p.equiv_type(&a, &b)?.0
            }
            (kind @ ("hcomp" | "comp"), [j, a, sides, base]) => {
                self.composition(kind == "hcomp", j, a, sides, base, names)?
            }
            ("transport", [i, a, x]) => call(
                "comp",
                [
                    self.term(a, &names.with_dimension(binder(i)?))?,
                    atom("ff"),
                    atom("zero"),
                    self.term(x, names)?,
                ],
            ),
            _ => return Err(format!("invalid term {s}")),
        })
    }

    /// Register a data declaration and return its generated theory text.
    fn declare(&mut self, head: &Sexp, ctors: &[Sexp]) -> Result<String> {
        // `NAME` or `(NAME PARAM...)`.
        let (name, params): (&str, Vec<&str>) = match head {
            Sexp::Atom(a) => (a, vec![]),
            Sexp::List(xs) if !xs.is_empty() => (
                xs[0].atom()?,
                xs[1..].iter().map(Sexp::atom).collect::<Result<_>>()?,
            ),
            _ => return Err(format!("invalid data head {head}")),
        };
        self.fresh(name)?;
        for (j, p) in params.iter().enumerate() {
            binder(&atom(p))?;
            if params[..j].contains(p) {
                return Err(format!("duplicate parameter {p}"));
            }
        }
        let ty = format!("ty/{name}");
        let mut out = Vec::new();
        let mut sources = Vec::new();
        for c in ctors {
            let xs = c.list()?;
            let cname = xs.first().ok_or("empty constructor")?.atom()?;
            self.fresh(cname)?;
            if out.iter().any(|o: &Ctor| o.name == cname) {
                return Err(format!("duplicate constructor {cname}"));
            }
            // A path constructor ends with `(path LEFT RIGHT)`.
            let (fields, boundary) = match xs.last() {
                Some(Sexp::List(ys))
                    if xs.len() > 1 && ys.first().is_some_and(|h| *h == atom("path")) =>
                {
                    let [_, l, r] = &ys[..] else {
                        return Err(format!("constructor {cname}: expected (path LEFT RIGHT)"));
                    };
                    (&xs[1..xs.len() - 1], Some((l.clone(), r.clone())))
                }
                _ => (&xs[1..], None),
            };
            let mut args = Vec::new();
            for a in fields {
                // Fields: discrete closed types, a parameter, or the type
                // itself at its own parameters (uniform recursion).
                let own = Sexp::List(
                    std::iter::once(atom(name))
                        .chain(params.iter().map(atom))
                        .collect(),
                );
                let arg = match a {
                    Sexp::Atom(n) if &**n == "bool" || &**n == "nat" => ArgTy::Closed(atom(n)),
                    Sexp::Atom(n) if &**n == name && params.is_empty() => ArgTy::Rec,
                    _ if !params.is_empty() && *a == own => ArgTy::Rec,
                    Sexp::Atom(n) if params.contains(&&**n) => {
                        ArgTy::Param(params.iter().position(|p| *p == &**n).unwrap())
                    }
                    Sexp::Atom(n) => match data::by_name(n) {
                        Some(d) if d.params == 0 => ArgTy::Closed(atom(&d.ty)),
                        _ => {
                            return Err(format!(
                                "field {n} must be bool, nat, a parameter, the type itself or an earlier closed data type"
                            ));
                        }
                    },
                    _ => return Err(format!("invalid field type {a}")),
                };
                args.push(arg);
            }
            if boundary.is_some() {
                if !params.is_empty() {
                    return Err(format!(
                        "{name}: path constructors need a type without parameters"
                    ));
                }
                if args.iter().any(|a| !matches!(a, ArgTy::Closed(_))) {
                    return Err(format!(
                        "path constructor {cname}: fields must be bool, nat or earlier closed data types"
                    ));
                }
            }
            out.push(Ctor {
                name: cname.to_owned(),
                symbol: format!("ctor/{name}/{cname}"),
                args,
                boundary: None,
            });
            sources.push(boundary);
        }
        if out.is_empty() {
            return Err(format!("data {name} needs a constructor"));
        }
        // Endpoints are closed point terms of the type, elaborated once all
        // constructors are known.
        for i in 0..out.len() {
            if let Some((l, r)) = &sources[i] {
                let l = self.endpoint(l, &out)?;
                let r = self.endpoint(r, &out)?;
                out[i].boundary = Some((l, r));
            }
        }
        let d = data::register(Data {
            name: name.to_owned(),
            ty,
            elim: format!("elim/{name}"),
            params: params.len(),
            ctors: out,
        });
        Ok(d.theory())
    }

    /// A path constructor's endpoint: a point constructor of the type being
    /// declared, applied to closed terms.
    fn endpoint(&mut self, s: &Sexp, ctors: &[Ctor]) -> Result<Sexp> {
        let (head, args) = match s {
            Sexp::Atom(a) => (&**a, &[][..]),
            Sexp::List(xs) if !xs.is_empty() => (xs[0].atom()?, &xs[1..]),
            _ => return Err(format!("invalid endpoint {s}")),
        };
        let c = ctors
            .iter()
            .find(|c| c.name == head && c.boundary.is_none())
            .ok_or_else(|| format!("endpoint {s} must be a point constructor of the type"))?;
        if args.len() != c.args.len() {
            return Err(format!(
                "endpoint {s}: {head} needs {} arguments",
                c.args.len()
            ));
        }
        let mut out = Vec::new();
        for (a, ty) in args.iter().zip(&c.args) {
            out.push(match ty {
                ArgTy::Rec => self.endpoint(a, ctors)?,
                _ => self.term(a, &Names::default())?,
            });
        }
        Ok(data::apply(&c.symbol, out))
    }

    fn fresh(&self, name: &str) -> Result<()> {
        if data::by_name(name).is_some() || data::by_ctor_name(name).is_some() {
            return Err(format!("{name} is already declared"));
        }
        if self.defs.contains_key(name) || self.prelude.contains_key(name) {
            return Err(format!("{name} is already defined"));
        }
        binder(&atom(name)).map(|_| ())
    }
}

/// Shift every universe by `level`: `(u n)` becomes `(u level+n)`.
fn relevel(t: &Sexp, level: &Sexp) -> Sexp {
    fn raise(n: &Sexp, level: &Sexp) -> Option<Sexp> {
        match n {
            Sexp::Atom(a) if &**a == "z" => Some(level.clone()),
            Sexp::List(xs) if xs.len() == 2 && xs[0] == atom("s") => {
                Some(call("s", [raise(&xs[1], level)?]))
            }
            _ => None,
        }
    }
    match t {
        Sexp::List(xs) if xs.len() == 2 && xs[0] == atom("u") && raise(&xs[1], level).is_some() => {
            call("u", [raise(&xs[1], level).unwrap()])
        }
        Sexp::List(xs) => super::engine::term::list(xs.iter().map(|x| relevel(x, level)).collect()),
        Sexp::Atom(_) => t.clone(),
    }
}

/// Pretty-print a closed core value: unary levels become decimal.
fn show(s: &Sexp) -> String {
    fn unary(s: &Sexp) -> Option<usize> {
        match s {
            Sexp::Atom(a) if &**a == "z" => Some(0),
            Sexp::List(xs) if xs.len() == 2 && xs[0] == atom("s") => unary(&xs[1]).map(|n| n + 1),
            _ => None,
        }
    }
    fn numeral(s: &Sexp) -> Option<usize> {
        match s {
            Sexp::Atom(a) if &**a == "zero" => Some(0),
            Sexp::List(xs) if xs.len() == 2 && xs[0] == atom("suc") => {
                numeral(&xs[1]).map(|n| n + 1)
            }
            _ => None,
        }
    }
    if let Some(n) = numeral(s) {
        return n.to_string();
    }
    match s {
        // Generated symbols print as the names they were declared with.
        Sexp::Atom(a) if a.starts_with("ctor/") || a.starts_with("ty/") => {
            a.rsplit('/').next().unwrap_or(a).to_string()
        }
        Sexp::Atom(a) => a.to_string(),
        Sexp::List(xs) => {
            let parts: Vec<_> = xs
                .iter()
                .enumerate()
                .map(|(i, x)| match unary(x) {
                    Some(n) if i > 0 => n.to_string(),
                    _ => show(x),
                })
                .collect();
            format!("({})", parts.join(" "))
        }
    }
}

/// Elaborate, certify and check a script, keeping its oracle.
pub fn run(source: &str) -> Result<Script> {
    run_with(source, Certificate::Oracle)
}

/// `run`, choosing whether the kernel checks an oracle or the derivation
/// itself; both are checked by the same kernel against the same goals.
pub fn run_with(source: &str, certificate: Certificate) -> Result<Script> {
    let source = source.to_owned();
    // Terms are interned per thread, so parsing happens on the worker.
    let (certified, evaluations) = certify(super::core_theory(), certificate, move || {
        let forms = parse(&source)?;
        data::clear();
        let mut appended = String::new();
        let mut e = Elaborator::new()?;
        let nil = atom("nil");
        let top = Face::True;
        let mut evaluations = Vec::new();
        let mut polymorphic = Vec::new();
        let mut names_seen = std::collections::HashSet::new();
        for form in &forms {
            // Number the holes in source order, wherever they are written.
            let mut written = Vec::new();
            let form = &number_holes(form, &mut written)?;
            e.holes = written.into_iter().map(|shown| (shown, None)).collect();
            let xs = form.list()?;
            let head = xs.first().ok_or("empty form")?.atom()?;
            // A data head may be `(NAME PARAM...)`.
            let name = match xs.get(1).ok_or("form needs a name")? {
                Sexp::List(h) if head == "data" && !h.is_empty() => h[0].atom()?.to_owned(),
                other => other.atom()?.to_owned(),
            };
            if !names_seen.insert(name.clone()) {
                return Err(format!("duplicate name {name}"));
            }
            let empty = Names::default();
            e.p.holes.clear();
            e.p.constraints.clear();
            e.level_marker = None;
            let what = format!("{head} {name}");
            match (head, &xs[2..]) {
                ("data", ctors) => appended.push_str(&e.declare(&xs[1], ctors)?),
                ("def-poly", [params, ty, t]) => {
                    e.fresh(&name)?;
                    let [param] = params.list()? else {
                        return Err(format!("def-poly {name}: exactly one level parameter"));
                    };
                    let param = binder(param)?.to_owned();
                    e.poly
                        .insert(name.clone(), (param.clone(), ty.clone(), t.clone()));
                    // With holes, check an instance at a level no script
                    // writes, so that goals show the level variable.
                    if !e.holes.is_empty() {
                        e.level_marker = Some((LEVEL_MARK, param.clone()));
                        let mark = super::engine::term::numeral(LEVEL_MARK);
                        let (tm, tym) = e.instance(&param, mark, ty, t)?;
                        let err =
                            e.p.check(0, &nil, &top, &tm, &tym)
                                .err()
                                .unwrap_or_default();
                        return Err(e.explain(&what, err));
                    }
                    // The instance at level 0 is an ordinary definition.
                    let (t0, ty0) = e.instance(&param, atom("z"), ty, t)?;
                    let id =
                        e.p.check(0, &nil, &top, &t0, &ty0)
                            .map_err(|err| e.explain(&format!("def-poly {name}"), err))?;
                    e.p.f.path.p.result(&name, id);
                    e.defs
                        .insert(name.clone(), call("ann", [t0.clone(), ty0.clone()]));
                    // The statement for every level, with L an eigenvariable.
                    let (tl, tyl) = e.instance(&param, atom("L"), ty, t)?;
                    let expected = call("rhas", [atom("z"), nil.clone(), atom("ft"), tl, tyl]);
                    let theory = super::core_theory() + &appended;
                    polymorphic.push(
                        generalize_definition(&name, &e.p.f.path.p, id, &expected, &theory)
                            .map_err(|err| e.explain(&format!("def-poly {name}"), err))?,
                    );
                }
                ("def", [ty, t]) => {
                    e.fresh(&name)?;
                    let ty = e.term(ty, &empty)?;
                    let t = e.term(t, &empty)?;
                    let id =
                        e.p.check(0, &nil, &top, &t, &ty)
                            .map_err(|err| e.explain(&format!("def {name}"), err))?;
                    e.p.f.path.p.result(&name, id);
                    e.defs.insert(name, call("ann", [t, ty]));
                }
                ("check", [t, ty]) => {
                    let ty = e.term(ty, &empty)?;
                    let t = e.term(t, &empty)?;
                    let id =
                        e.p.check(0, &nil, &top, &t, &ty)
                            .map_err(|err| e.explain(&format!("check {name}"), err))?;
                    e.p.f.path.p.result(&name, id);
                }
                ("eval", [t, rest @ ..]) if rest.len() <= 1 => {
                    let t = e.term(t, &empty)?;
                    let ty = match rest {
                        [ty] => e.term(ty, &empty)?,
                        _ => {
                            // Report the inferred type in weak-head normal form.
                            let (ty, _) =
                                e.p.infer(0, &nil, &top, &t)
                                    .map_err(|err| e.explain(&format!("eval {name}"), err))?;
                            let (universe, _) =
                                e.p.infer(0, &nil, &top, &ty)
                                    .map_err(|err| e.explain(&format!("eval {name}"), err))?;
                            e.p.value(0, &nil, &top, &ty, &universe, FUEL)
                                .map_err(|err| e.explain(&format!("eval {name}"), err))?
                                .0
                        }
                    };
                    let (value, id) =
                        e.p.value(0, &nil, &top, &t, &ty, FUEL)
                            .map_err(|err| e.explain(&format!("eval {name}"), err))?;
                    e.p.f.path.p.result(&name, id);
                    evaluations.push(Evaluation {
                        name,
                        value: show(&value),
                        ty: show(&ty),
                    });
                }
                ("equal", [a, b, ty]) => {
                    let (a, b, ty) = (e.term(a, &empty)?, e.term(b, &empty)?, e.term(ty, &empty)?);
                    let id =
                        e.p.equality(0, &nil, &top, &a, &b, &ty)
                            .map_err(|err| e.explain(&format!("equal {name}"), err))?;
                    e.p.f.path.p.result(&name, id);
                }
                _ => return Err(format!("invalid form {form}")),
            }
            // Checking goes past holes to find them all; a form with one is
            // reported, never certified.
            if !e.holes.is_empty() {
                return Err(e.explain(&what, String::new()));
            }
        }
        Ok((e.p, (evaluations, polymorphic), appended))
    })?;
    let (evaluations, polymorphic) = evaluations;
    Ok(Script {
        certified,
        evaluations,
        polymorphic,
    })
}

/// Replace each hole `?` or `(? NAME)` of a form by `(?# K)`, numbering them
/// in the order they are written, and collect how each is shown.
fn number_holes(s: &Sexp, written: &mut Vec<String>) -> Result<Sexp> {
    match s {
        Sexp::Atom(a) if &**a == "?" => {
            let k = written.len();
            written.push(format!("?{}", k + 1));
            Ok(call("?#", [atom(k.to_string())]))
        }
        Sexp::List(xs) if xs.first().and_then(|h| h.atom().ok()) == Some("?") => {
            let [_, name] = &xs[..] else {
                return Err(format!("invalid hole {s}"));
            };
            let k = written.len();
            written.push(format!("?{}", binder(name)?));
            Ok(call("?#", [atom(k.to_string())]))
        }
        Sexp::List(xs) => Ok(super::engine::term::list(
            xs.iter()
                .map(|x| number_holes(x, written))
                .collect::<Result<_>>()?,
        )),
        Sexp::Atom(_) => Ok(s.clone()),
    }
}
