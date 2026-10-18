//! Oracle certificates: whatever the decoder produces is checked by the
//! kernel, so these tests check that encoding then decoding reproduces an
//! accepted certificate, and that corrupt oracles end in an error, never a
//! panic or a hang.
use horn::{compress::compress, kernel::Theory, oracle};

const THEORY: &str = "(sort A) (sort B)
    (ctor z () A) (ctor s (A) A) (ctor pair (A A) B) (ctor q () B)
    (pred le (A A)) (pred ok (B)) (pred s (A)) (pred top ())
    (rule le.z () (le z ?n))
    (rule le.s ((le ?m ?n)) (le (s ?m) (s ?n)))
    (rule mk ((le ?a ?b)) (ok (pair ?a ?b)))
    (rule pick ((ok (pair ?a ?b)) (ok (pair ?b ?c))) (ok (pair ?a ?c)))
    (rule refl ((le ?a ?a)) (s ?a))
    (rule top () (top))
    (rule from-top ((top)) (ok q))";

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

fn number(rng: &mut Rng) -> String {
    (0..rng.below(4)).fold("z".to_owned(), |t, _| format!("(s {t})"))
}

/// Strip `(op ARG)` to ARG, or `None` when `t` has another shape.
fn inside<'a>(t: &'a str, op: &str) -> Option<&'a str> {
    t.strip_prefix(&format!("({op} "))?.strip_suffix(')')
}

/// Split the two top-level arguments of `(op X Y)`.
fn pair<'a>(t: &'a str, op: &str) -> Option<(&'a str, &'a str)> {
    let body = inside(t, op)?;
    let mut depth = 0;
    for (i, c) in body.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            ' ' if depth == 0 => return Some((&body[..i], &body[i + 1..])),
            _ => {}
        }
    }
    None
}

/// A random ordinary certificate built by forward chaining, with goals taken
/// from what it derived.
fn random_certificate(rng: &mut Rng) -> (String, String) {
    let mut facts: Vec<String> = Vec::new();
    let mut proof = String::new();
    for _ in 0..2 + rng.below(40) {
        let pick = |rng: &mut Rng, facts: &[String], f: &dyn Fn(&str) -> bool| {
            let found: Vec<usize> = (0..facts.len()).filter(|&i| f(&facts[i])).collect();
            (!found.is_empty()).then(|| found[rng.below(found.len())])
        };
        let (rule, refs, fact) = match rng.below(7) {
            0 => ("le.z", vec![], format!("(le z {})", number(rng))),
            1 => match pick(rng, &facts, &|f| f.starts_with("(le ")) {
                Some(i) => {
                    let (m, n) = pair(&facts[i], "le").unwrap();
                    ("le.s", vec![i], format!("(le (s {m}) (s {n}))"))
                }
                None => continue,
            },
            2 => match pick(rng, &facts, &|f| f.starts_with("(le ")) {
                Some(i) => {
                    let (a, b) = pair(&facts[i], "le").unwrap();
                    ("mk", vec![i], format!("(ok (pair {a} {b}))"))
                }
                None => continue,
            },
            3 => {
                let Some(i) = pick(rng, &facts, &|f| f.starts_with("(ok (pair ")) else {
                    continue;
                };
                let (a, b) = pair(inside(&facts[i], "ok").unwrap(), "pair").unwrap();
                let (a, b) = (a.to_owned(), b.to_owned());
                let second = pick(rng, &facts, &|f| {
                    inside(f, "ok")
                        .and_then(|p| pair(p, "pair"))
                        .is_some_and(|(x, _)| x == b)
                });
                let Some(j) = second else { continue };
                let (_, c) = pair(inside(&facts[j], "ok").unwrap(), "pair").unwrap();
                ("pick", vec![i, j], format!("(ok (pair {a} {c}))"))
            }
            4 => match pick(rng, &facts, &|f| pair(f, "le").is_some_and(|(a, b)| a == b)) {
                Some(i) => (
                    "refl",
                    vec![i],
                    format!("(s {})", pair(&facts[i], "le").unwrap().0),
                ),
                None => continue,
            },
            5 => ("top", vec![], "(top)".to_owned()),
            _ => match pick(rng, &facts, &|f| f == "(top)") {
                Some(i) => ("from-top", vec![i], "(ok q)".to_owned()),
                None => continue,
            },
        };
        let refs: Vec<String> = refs.iter().map(usize::to_string).collect();
        proof += &format!(
            "(step {} {rule} ({}) {fact})\n",
            facts.len(),
            refs.join(" ")
        );
        facts.push(fact);
    }
    if facts.is_empty() {
        proof += "(step 0 top () (top))\n";
        facts.push("(top)".to_owned());
    }
    let mut goals = String::new();
    let mut chosen: Vec<&String> = Vec::new();
    for g in 0..1 + rng.below(3) {
        let i = rng.below(facts.len());
        if !chosen.contains(&&facts[i]) {
            chosen.push(&facts[i]);
            goals += &format!("(goal g{g} {})\n", facts[i]);
            proof += &format!("(result g{g} {i})\n");
        }
    }
    (goals, proof)
}

fn roundtrip(theory: &str, goals: &str, proof: &str) -> (Vec<u8>, String) {
    let (bytes, stats) = oracle::encode(theory, goals, proof.as_bytes()).unwrap();
    let mut out = Vec::new();
    let decoded = oracle::decode(theory, goals, &bytes, &mut out).unwrap();
    assert_eq!(stats.steps, decoded.steps);
    (bytes, String::from_utf8(out).unwrap())
}

#[test]
fn the_example_round_trips_through_the_kernel() {
    let theory = include_str!("../examples/nat.horn");
    let goals = include_str!("../examples/nat.goals");
    for proof in [
        include_str!("../examples/nat.proof"),
        include_str!("../examples/nat.compact.proof"),
    ] {
        let (bytes, text) = roundtrip(theory, goals, proof);
        let report = Theory::parse(theory).unwrap().check(goals, &text).unwrap();
        assert_eq!((report.goals, report.steps), (1, 3));
        assert!(bytes.len() < 32, "{} bytes", bytes.len());
    }
}

#[test]
fn random_certificates_round_trip_through_the_kernel() {
    let theory = Theory::parse(THEORY).unwrap();
    let (mut rng, mut witnesses) = (Rng(0x5eed_0f0a_c1e5), 0);
    for case in 0..3000 {
        let (goals, proof) = random_certificate(&mut rng);
        theory
            .check(&goals, &proof)
            .unwrap_or_else(|e| panic!("{case}: generator: {e}\n{proof}"));
        let (bytes, text) = roundtrip(THEORY, &goals, &proof);
        let report = theory
            .check(&goals, &text)
            .unwrap_or_else(|e| panic!("{case}: {e}\n{proof}\n=>\n{text}"));
        assert!(report.steps <= proof.lines().count());
        // Compact input describes the same derivation without duplicates.
        let mut compact = Vec::new();
        compress(THEORY, proof.as_bytes(), &mut compact).unwrap();
        let (_, text) = roundtrip(THEORY, &goals, std::str::from_utf8(&compact).unwrap());
        theory.check(&goals, &text).unwrap();
        witnesses += oracle::encode(THEORY, &goals, proof.as_bytes())
            .unwrap()
            .1
            .witnesses;
        assert!(bytes.len() < proof.len());
    }
    // The generator exercises conclusions left open by their premises.
    assert!(witnesses > 50, "{witnesses}");
}

#[test]
fn corrupt_oracles_fail_cleanly() {
    let theory = Theory::parse(THEORY).unwrap();
    let mut rng = Rng(0x0bad_0dd5_eed0);
    let (mut decoded, mut accepted) = (0, 0);
    for _ in 0..3000 {
        let (goals, proof) = random_certificate(&mut rng);
        let (mut bytes, _) = oracle::encode(THEORY, &goals, proof.as_bytes()).unwrap();
        match rng.below(3) {
            0 => bytes.truncate(14 + rng.below(bytes.len() - 13)),
            1 => {
                let i = 14 + rng.below(bytes.len() - 14);
                bytes[i] ^= 1 << rng.below(8);
            }
            _ => bytes.extend((0..1 + rng.below(16)).map(|_| rng.next() as u8)),
        }
        let mut out = Vec::new();
        if oracle::decode(THEORY, &goals, &bytes, &mut out).is_ok() {
            decoded += 1;
            // Acceptance of a decoded certificate is sound regardless of how
            // the oracle was damaged; the kernel decides.
            accepted += usize::from(
                theory
                    .check(&goals, std::str::from_utf8(&out).unwrap())
                    .is_ok(),
            );
        }
    }
    assert!(decoded > 0 && accepted > 0, "{decoded} {accepted}");
    let mut out = Vec::new();
    assert!(oracle::decode(THEORY, "(goal g (top))", b"not an oracle", &mut out).is_err());
}

#[test]
fn unbounded_forced_reconstruction_stops_with_an_error() {
    // Every subgoal has exactly one candidate, so no oracle bits are read.
    let theory = "(sort N) (ctor z () N) (ctor s (N) N) (pred p (N))
        (rule up ((p (s ?x))) (p ?x))";
    let error =
        oracle::decode(theory, "(goal g (p z))", b"horn-oracle 1\n", Vec::new()).unwrap_err();
    assert!(error.contains("nesting"), "{error}");
}

#[test]
fn oracles_decode_unchanged_after_declarations_are_appended() {
    // The extension competes with old candidates: a new A constructor for
    // witnesses and new rules for le and ok, which would change every coded
    // choice if the decoder considered them.
    let extended = format!(
        "{THEORY}
        (ctor w () A)
        (rule le.w () (le w ?n))
        (rule le.back ((le (s ?m) (s ?n))) (le ?m ?n))
        (rule ok.any ((le ?a ?a)) (ok (pair ?a ?a)))"
    );
    let theory = Theory::parse(&extended).unwrap();
    let mut rng = Rng(0x0e7e_d5ed_0a11);
    let mut unrestricted_failures = 0;
    for case in 0..500 {
        let (goals, proof) = random_certificate(&mut rng);
        let (bytes, _) = oracle::encode(THEORY, &goals, proof.as_bytes()).unwrap();
        // The same decisions under a version 1 header, which records no
        // theory size, are read against the whole extended theory.
        let mut v1 = b"horn-oracle 1\n".to_vec();
        v1.extend(&bytes[22..]);
        unrestricted_failures += usize::from(oracle::check(&extended, &goals, &v1).is_err());
        let mut out = Vec::new();
        oracle::decode(&extended, &goals, &bytes, &mut out)
            .unwrap_or_else(|e| panic!("{case}: {e}\n{proof}"));
        theory
            .check(&goals, std::str::from_utf8(&out).unwrap())
            .unwrap_or_else(|e| panic!("{case}: {e}"));
        // The full check helper streams the same decoding into the kernel.
        oracle::check(&extended, &goals, &bytes).unwrap();
    }
    assert!(unrestricted_failures > 250, "{unrestricted_failures}");
    // An oracle names the theory size it needs; a smaller theory is refused.
    let (goals, proof) = random_certificate(&mut rng);
    let (bytes, _) = oracle::encode(&extended, &goals, proof.as_bytes()).unwrap();
    let error = oracle::decode(THEORY, &goals, &bytes, Vec::new()).unwrap_err();
    assert!(error.contains("larger theory"), "{error}");
}
