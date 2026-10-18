//! Check an oracle certificate: an untrusted thread decodes it into a compact
//! certificate and streams that through a pipe into the unchanged kernel.
use horn::oracle;
use std::{env, fs, process, time::Instant};

fn run() -> Result<(), String> {
    let args: Vec<_> = env::args().collect();
    if args.len() != 4 {
        return Err("usage: oracle-kernel THEORY GOALS ORACLE".into());
    }
    let read = |p: &str| fs::read_to_string(p).map_err(|e| e.to_string());
    let (source, goals) = (read(&args[1])?, read(&args[2])?);
    let oracle = fs::read(&args[3]).map_err(|e| e.to_string())?;
    let start = Instant::now();
    let report = oracle::check(&source, &goals, &oracle)?;
    println!(
        "ACCEPT (oracle): {} goals, {} proof steps from {} oracle bytes, {} distinct terms, {:?}",
        report.goals,
        report.steps,
        oracle.len(),
        report.terms,
        start.elapsed()
    );
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("REJECT: {e}");
        process::exit(1);
    }
}
