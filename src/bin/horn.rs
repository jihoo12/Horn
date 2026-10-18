//! Run a Horn source file: elaborate it, evaluate and prove, and check the
//! resulting certificate. See `horn::lang`.
use horn::{cubical, lang, oracle, schematic};
use std::{env, fs, process};

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();
    if args.get(1).is_some_and(|arg| arg == "cubical") {
        return run_cubical(&args[2..]);
    }
    let usage = "usage: horn FILE.hn [--emit DIR] [--agda MODULE OUT.agda]\n       horn cubical list|check NAME|export NAME DIR";
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

fn run_cubical(args: &[String]) -> Result<(), String> {
    let usage = "usage: horn cubical list\n       horn cubical check NAME|all\n       horn cubical export NAME DIR";
    let args: Vec<_> = args.iter().map(String::as_str).collect();
    if args == ["list"] {
        for example in cubical::EXAMPLES {
            println!("{}: {}", example.name, example.description);
        }
        return Ok(());
    }
    match args.as_slice() {
        ["check", name] => {
            let selected: Vec<_> = cubical::EXAMPLES
                .iter()
                .filter(|example| *name == "all" || example.name == *name)
                .collect();
            if selected.is_empty() {
                return Err(format!(
                    "unknown cubical example {name}; use `horn cubical list`"
                ));
            }
            let theory = cubical::theory();
            for example in selected {
                let report = oracle::check(&theory, example.goals, example.oracle)?;
                println!(
                    "ACCEPT (cubical {}): {} goals, {} proof steps, {} oracle bytes",
                    example.name,
                    report.goals,
                    report.steps,
                    example.oracle.len()
                );
            }
        }
        ["export", name, dir] => {
            let example = cubical::EXAMPLES
                .iter()
                .find(|example| example.name == *name)
                .ok_or_else(|| {
                    format!("unknown cubical example {name}; use `horn cubical list`")
                })?;
            // A new directory prevents overwriting the caller's theory/goals.
            fs::create_dir(dir).map_err(|e| format!("cannot create new directory {dir}: {e}"))?;
            let dir = std::path::Path::new(dir);
            fs::write(dir.join("theory.horn"), cubical::theory()).map_err(|e| e.to_string())?;
            fs::write(dir.join("goals"), example.goals).map_err(|e| e.to_string())?;
            fs::write(dir.join("proof.oracle"), example.oracle).map_err(|e| e.to_string())?;
            println!(
                "exported {} to {} (not checked by export)",
                example.name,
                dir.display()
            );
        }
        _ => return Err(usage.into()),
    }
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("error: {e}");
        process::exit(1);
    }
}
