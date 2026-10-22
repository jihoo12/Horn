//! Regenerate the bundled cubical examples with the engine and certify
//! them. The derivation streams from the producer through a pipe, either to
//! the oracle encoder (the result is then checked by `oracle::check` against
//! the fixed theory and goals) or straight to the kernel; no proof file is
//! materialized.
use super::engine::restricted_frontend::RestrictedProducer;
use super::engine::{canonicity_frontend, deep_univalence_frontend, ua_transport_frontend};
use crate::kernel::Report;
use crate::oracle;
use crate::sexp::Result;
use std::io::{BufWriter, Write};

/// Producer recursion follows the term structure, which is deep.
const STACK_BYTES: usize = 1 << 30;

/// Builds a bundled example's derivation.
pub type Generator = fn() -> Result<RestrictedProducer>;

pub const GENERATORS: &[(&str, Generator)] = &[
    ("univalence", deep_univalence_frontend::deep_univalence_demo),
    ("ua-transport", ua_transport_frontend::ua_transport_demo),
    ("canonicity", canonicity_frontend::canonicity_demo),
];

pub struct Regenerated {
    /// The theory the derivation was checked against.
    pub theory: String,
    /// The theory rules the accepted derivation uses, sorted. Only these
    /// rules' meaning matters for the goals; the rest of the theory does not.
    pub rules_used: Vec<String>,
    pub goals: String,
    /// The checked oracle, when one was asked for.
    pub oracle: Option<Vec<u8>>,
    pub checked: Report,
}

/// What `certify` hands the kernel.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Certificate {
    /// Encode the derivation as an oracle and check the decoded oracle: the
    /// portable certificate itself is what the kernel accepted.
    Oracle,
    /// Stream the derivation to the kernel as compact proof text. The same
    /// kernel checks the same steps, without encoding and decoding an oracle.
    Direct,
}

/// Run `produce` on a large stack and check the results it registered as
/// goals with the kernel, through an oracle or directly (`Certificate`).
/// `produce` also returns theory text to append to the bundled theory
/// (generated data declarations); the derivation is checked against the
/// combined theory.
pub fn certify<T: Send>(
    base: String,
    certificate: Certificate,
    produce: impl FnOnce() -> Result<(RestrictedProducer, T, String)> + Send,
) -> Result<(Regenerated, T)> {
    let (theory, goals, extra, outcome) = std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .stack_size(STACK_BYTES)
            .spawn_scoped(scope, || -> Result<_> {
                let (p, extra, appended) = produce()?;
                let theory = base.clone() + &appended;
                let steps = &p.f.path.p;
                let goals: String = steps
                    .results()
                    .iter()
                    .map(|(name, id)| format!("(goal {name} {})\n", steps.judgment(*id)))
                    .collect();
                // Debugging aid: also write the compact certificate to a file.
                if let Ok(path) = std::env::var("HORN_DUMP_PROOF") {
                    let file = std::fs::File::create(&path).map_err(|e| format!("{path}: {e}"))?;
                    let mut file = BufWriter::new(file);
                    steps
                        .write_reachable(&mut file)
                        .and_then(|_| file.flush())
                        .map_err(|e| e.to_string())?;
                    std::fs::write(format!("{path}.goals"), &goals).map_err(|e| e.to_string())?;
                }
                // The kernel checks a direct derivation as it streams out of
                // the producer; an oracle is checked after the producer's
                // memory is released.
                let outcome = match certificate {
                    Certificate::Oracle => Outcome::Encoded(encode(steps, &theory, &goals)?),
                    Certificate::Direct => {
                        Outcome::Checked(oracle::check_text_with_rules(&theory, &goals, |out| {
                            steps
                                .write_reachable(out)
                                .map(drop)
                                .map_err(|e| e.to_string())
                        })?)
                    }
                };
                Ok((theory, goals, extra, outcome))
            })
            .map_err(|e| e.to_string())?;
        worker.join().map_err(|_| "producer panicked".to_string())?
    })?;
    let (oracle, (checked, rules_used)) = match outcome {
        Outcome::Checked(checked) => (None, checked),
        Outcome::Encoded(oracle) => {
            let checked = oracle::check_with_rules(&theory, &goals, &oracle)?;
            (Some(oracle), checked)
        }
    };
    Ok((
        Regenerated {
            goals,
            oracle,
            checked,
            theory,
            rules_used,
        },
        extra,
    ))
}

enum Outcome {
    Checked((Report, Vec<String>)),
    Encoded(Vec<u8>),
}

/// Stream the producer's reachable derivation into the oracle encoder.
fn encode(steps: &super::engine::frontend::Producer, theory: &str, goals: &str) -> Result<Vec<u8>> {
    let (reader, mut writer) = crate::pipe::pipe();
    std::thread::scope(|inner| -> Result<Vec<u8>> {
        let encoder = inner.spawn(|| oracle::encode(theory, goals, reader));
        let written = steps
            .write_reachable(&mut writer)
            .and_then(|_| writer.flush())
            .map_err(|e| e.to_string());
        drop(writer);
        let encoded = encoder.join().map_err(|_| "encoder panicked")?;
        // An encoder failure closes the pipe; report its cause.
        let encoded = encoded?;
        written?;
        Ok(encoded.0)
    })
}

/// The number of rules a theory declares.
pub fn rule_count(theory: &str) -> usize {
    crate::sexp::parse(theory)
        .map(|forms| {
            forms
                .iter()
                .filter(|f| f.list().ok().and_then(|xs| xs.first()?.atom().ok()) == Some("rule"))
                .count()
        })
        .unwrap_or(0)
}

pub fn regenerate(name: &str) -> Result<Regenerated> {
    let (_, produce) = GENERATORS
        .iter()
        .find(|(n, _)| *n == name)
        .ok_or_else(|| format!("no generator for cubical example {name}"))?;
    let produce = *produce;
    Ok(certify(super::theory(), Certificate::Oracle, || {
        Ok((produce()?, (), String::new()))
    })?
    .0)
}
