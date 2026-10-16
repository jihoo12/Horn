use horn::kernel::Theory;
use std::{env, fs, process, time::Instant};

fn run() -> Result<(), String> {
    let args: Vec<_> = env::args().collect();
    if args.len() != 4 {
        return Err("usage: kernel THEORY GOALS PROOF".into());
    }
    let read = |p: &str| fs::read_to_string(p).map_err(|e| format!("{p}: {e}"));
    let theory = Theory::parse(&read(&args[1])?)?;
    let goals = read(&args[2])?;
    let proof = read(&args[3])?;
    let start = Instant::now();
    let report = theory.check(&goals, &proof)?;
    println!(
        "ACCEPT: {} goals, {} proof steps, {} bytes, {:?}",
        report.goals,
        report.steps,
        proof.len(),
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
