//! Untrusted tool: rewrite a certificate into compact form. Check the output.
use horn::compress::compress;
use std::{
    env,
    fs::{self, File},
    io::{BufReader, BufWriter},
    process,
};

fn run() -> Result<(), String> {
    let args: Vec<_> = env::args().collect();
    if args.len() != 4 {
        return Err("usage: horn-compress THEORY PROOF OUTPUT".into());
    }
    let theory = fs::read_to_string(&args[1]).map_err(|e| format!("{}: {e}", args[1]))?;
    let input = File::open(&args[2]).map_err(|e| format!("{}: {e}", args[2]))?;
    let output = File::create(&args[3]).map_err(|e| format!("{}: {e}", args[3]))?;
    let stats = compress(&theory, BufReader::new(input), BufWriter::new(output))?;
    eprintln!(
        "GENERATED (not checked): {} of {} steps kept ({} duplicate, {} unused), {} definitions",
        stats.output_steps,
        stats.input_steps,
        stats.duplicate_steps,
        stats.unused_steps,
        stats.definitions
    );
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("ERROR: {e}");
        process::exit(1);
    }
}
