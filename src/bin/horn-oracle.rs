//! Untrusted oracle encoder and decoder; see `horn::oracle`.
use horn::oracle::{decode, encode};
use std::{env, fs, fs::File, io::BufReader, io::BufWriter, process};

fn run() -> Result<(), String> {
    let args: Vec<_> = env::args().collect();
    let read = |p: &str| fs::read_to_string(p).map_err(|e| e.to_string());
    let open = |p: &str| File::open(p).map_err(|e| e.to_string());
    let create = |p: &str| File::create(p).map_err(|e| e.to_string());
    match args.get(1).map(String::as_str) {
        Some("encode") if args.len() == 6 => {
            let proof = BufReader::with_capacity(1 << 20, open(&args[4])?);
            let (bytes, stats) = encode(&read(&args[2])?, &read(&args[3])?, proof)?;
            fs::write(&args[5], &bytes).map_err(|e| e.to_string())?;
            eprintln!(
                "GENERATED (not checked): {} goals, {} steps, {} decisions, {} witnesses, depth {} -> {} bytes",
                stats.goals,
                stats.steps,
                stats.decisions,
                stats.witnesses,
                stats.depth,
                stats.oracle_bytes
            );
            if stats.choices > 0 {
                eprintln!(
                    "model: {} choices among several candidates, most probable taken {} ({:.1}%), ranks {:?}",
                    stats.choices,
                    stats.top1,
                    100.0 * stats.top1 as f64 / stats.choices as f64,
                    stats.rank_hist
                );
            }
        }
        Some("decode") if args.len() == 6 => {
            let oracle = fs::read(&args[4]).map_err(|e| e.to_string())?;
            let out = BufWriter::with_capacity(1 << 20, create(&args[5])?);
            let stats = decode(&read(&args[2])?, &read(&args[3])?, &oracle, out)?;
            eprintln!(
                "GENERATED (not checked): {} goals, {} steps from {} oracle bytes",
                stats.goals, stats.steps, stats.oracle_bytes
            );
        }
        _ => {
            return Err(
                "usage: horn-oracle encode THEORY GOALS PROOF ORACLE\n       \
                        horn-oracle decode THEORY GOALS ORACLE PROOF"
                    .into(),
            );
        }
    }
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("ERROR: {e}");
        process::exit(1);
    }
}
