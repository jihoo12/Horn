//! Run a Horn source file: elaborate it, evaluate and prove, and check the
//! resulting certificate. See `horn::lang`.
use horn::{lang, schematic};
use std::{env, fs, process};

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();
    let usage = "usage: horn FILE.hn [--emit DIR] [--agda MODULE OUT.agda]";
    let path = args.get(1).ok_or(usage)?;
    let src = fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    let r = lang::run(&src)?;
    for line in &r.report {
        println!("{line}");
    }
    println!(
        "certificate accepted: {} goals, {} steps, {} inductions",
        r.checked.goals, r.checked.steps, r.checked.inductions
    );
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--emit" => {
                let dir = args.get(i + 1).ok_or(usage)?;
                fs::create_dir_all(dir).map_err(|e| e.to_string())?;
                for (name, text) in [
                    ("theory.horn", &r.theory),
                    ("goals", &r.goals),
                    ("proof", &r.proof),
                ] {
                    fs::write(format!("{dir}/{name}"), text).map_err(|e| e.to_string())?;
                }
                i += 2;
            }
            "--agda" => {
                let (module, out) = (args.get(i + 1).ok_or(usage)?, args.get(i + 2).ok_or(usage)?);
                let mut buf = Vec::new();
                schematic::export_agda(&r.theory, &r.goals, r.proof.as_bytes(), module, &mut buf)?;
                fs::write(out, buf).map_err(|e| e.to_string())?;
                i += 3;
            }
            _ => return Err(usage.into()),
        }
    }
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("error: {e}");
        process::exit(1);
    }
}
