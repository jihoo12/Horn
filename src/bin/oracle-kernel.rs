//! Check an oracle certificate: an untrusted thread decodes it into a compact
//! certificate and streams that through a pipe into the unchanged kernel.
use horn::kernel::Theory;
use horn::oracle::decode;
use std::io::{BufReader, BufWriter};
use std::{env, fs, process, thread, time::Instant};

fn run() -> Result<(), String> {
    let args: Vec<_> = env::args().collect();
    if args.len() != 4 {
        return Err("usage: oracle-kernel THEORY GOALS ORACLE".into());
    }
    let read = |p: &str| fs::read_to_string(p).map_err(|e| e.to_string());
    let (source, goals) = (read(&args[1])?, read(&args[2])?);
    let oracle = fs::read(&args[3]).map_err(|e| e.to_string())?;
    let theory = Theory::parse(&source)?;
    let start = Instant::now();
    let (reader, writer) = std::io::pipe().map_err(|e| e.to_string())?;
    let (report, decoded) = thread::scope(|s| {
        let decoder = s.spawn(|| {
            decode(
                &source,
                &goals,
                &oracle,
                BufWriter::with_capacity(1 << 20, writer),
            )
        });
        let report = theory.check_reader(&goals, BufReader::with_capacity(1 << 20, reader));
        (report, decoder.join())
    });
    let decoded = decoded.map_err(|_| "decoder panicked".to_string())?;
    // A kernel rejection explains more than the decoder's broken pipe.
    let report = report?;
    decoded?;
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
