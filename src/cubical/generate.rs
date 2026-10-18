//! Regenerate the bundled cubical examples with the engine and encode them
//! straight into oracles. The derivation streams from the producer to the
//! encoder through a pipe, so no proof file is materialized; the result is
//! then checked by `oracle::check` against the fixed theory and goals.
use super::engine::restricted_frontend::RestrictedProducer;
use super::engine::{canonicity_frontend, deep_univalence_frontend, ua_transport_frontend};
use crate::kernel::Report;
use crate::oracle;
use crate::sexp::Result;
use std::io::{BufReader, BufWriter, Write};

/// Producer recursion follows the term structure, which is deep.
const STACK_BYTES: usize = 1 << 30;

pub const GENERATORS: &[(&str, fn() -> Result<RestrictedProducer>)] = &[
    ("univalence", deep_univalence_frontend::deep_univalence_demo),
    ("ua-transport", ua_transport_frontend::ua_transport_demo),
    ("canonicity", canonicity_frontend::canonicity_demo),
];

pub struct Regenerated {
    pub goals: String,
    pub oracle: Vec<u8>,
    pub checked: Report,
}

pub fn regenerate(name: &str) -> Result<Regenerated> {
    let (_, produce) = GENERATORS
        .iter()
        .find(|(n, _)| *n == name)
        .ok_or_else(|| format!("no generator for cubical example {name}"))?;
    let produce = *produce;
    let theory = super::theory();
    let (goals, oracle) = std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .stack_size(STACK_BYTES)
            .spawn_scoped(scope, || -> Result<(String, Vec<u8>)> {
                let p = produce()?;
                let steps = &p.f.path.p;
                let goals: String = steps
                    .results()
                    .iter()
                    .map(|(name, id)| format!("(goal {name} {})\n", steps.judgment(*id)))
                    .collect();
                let (reader, writer) = std::io::pipe().map_err(|e| e.to_string())?;
                std::thread::scope(|inner| {
                    let encoder = inner.spawn(|| {
                        oracle::encode(&theory, &goals, BufReader::with_capacity(1 << 20, reader))
                    });
                    let mut writer = BufWriter::with_capacity(1 << 20, writer);
                    let written = steps
                        .write_reachable(&mut writer)
                        .and_then(|_| writer.flush())
                        .map_err(|e| e.to_string());
                    drop(writer);
                    let encoded = encoder.join().map_err(|_| "encoder panicked")?;
                    written?;
                    Ok((goals.clone(), encoded?.0))
                })
            })
            .map_err(|e| e.to_string())?;
        worker.join().map_err(|_| "producer panicked".to_string())?
    })?;
    let checked = oracle::check(&theory, &goals, &oracle)?;
    Ok(Regenerated {
        goals,
        oracle,
        checked,
    })
}
