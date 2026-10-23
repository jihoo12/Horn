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
    // The process exits after one command; leave the term table to the OS.
    cubical::engine::term::keep_terms_until_exit();
    let usage = "usage: horn cubical list\n       horn cubical check NAME|all\n       horn cubical export NAME DIR\n       horn cubical run FILE [--profile NAME] [--emit NEW_DIR]\n       horn cubical generate NAME [--emit NEW_DIR]\n       horn cubical eval FILE.hcs [--emit NEW_DIR]";
    let args: Vec<_> = args.iter().map(String::as_str).collect();
    if args == ["list"] {
        for example in cubical::EXAMPLES {
            println!("{}: {}", example.name, example.description);
        }
        return Ok(());
    }
    match args.as_slice() {
        ["run", path, options @ ..] => {
            let (mut profile, mut output) = (None, None);
            let mut i = 0;
            while i < options.len() {
                match options.get(i..i + 2) {
                    Some(["--profile", name]) if profile.is_none() => {
                        profile = Some(cubical::producer::Profile::parse(name)?);
                    }
                    Some(["--emit", dir]) if output.is_none() => output = Some(*dir),
                    _ => return Err(usage.into()),
                }
                i += 2;
            }
            let source = fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
            let generated = match profile {
                Some(profile) => cubical::source::run_with_profile(&source, profile),
                None => cubical::source::run(&source),
            }
            .map_err(|e| format!("{path}: {e}"))?;
            if let Some(dir) = output {
                fs::create_dir(dir)
                    .map_err(|e| format!("cannot create new directory {dir}: {e}"))?;
                let dir = std::path::Path::new(dir);
                for (name, contents) in [
                    ("theory.horn", generated.theory.as_str()),
                    ("goals", generated.goals.as_str()),
                    ("proof", generated.proof.as_str()),
                ] {
                    fs::write(dir.join(name), contents).map_err(|e| e.to_string())?;
                }
            }
            println!(
                "ACCEPT (generated cubical): {} goals, {} proof steps",
                generated.checked.goals, generated.checked.steps
            );
        }
        ["eval", path, rest @ ..] => {
            let output = match rest {
                [] => None,
                ["--emit", dir] => Some(*dir),
                _ => return Err(usage.into()),
            };
            if let Some(dir) = output
                && std::path::Path::new(dir).exists()
            {
                return Err(format!("{dir} already exists"));
            }
            let source = fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
            // An oracle is only built when it is written out; otherwise the
            // kernel checks the derivation as the engine streams it.
            let certificate = match output {
                Some(_) => cubical::generate::Certificate::Oracle,
                None => cubical::generate::Certificate::Direct,
            };
            let script = cubical::script::run_with(&source, certificate)
                .map_err(|e| format!("{path}: {e}"))?;
            if let Some(dir) = output {
                fs::create_dir(dir)
                    .map_err(|e| format!("cannot create new directory {dir}: {e}"))?;
                let dir = std::path::Path::new(dir);
                fs::write(dir.join("theory.horn"), &script.certified.theory)
                    .map_err(|e| e.to_string())?;
                fs::write(dir.join("goals"), &script.certified.goals).map_err(|e| e.to_string())?;
                let oracle = script.certified.oracle.as_deref().ok_or("no oracle")?;
                fs::write(dir.join("proof.oracle"), oracle).map_err(|e| e.to_string())?;
            }
            if let Some(dir) = output {
                let dir = std::path::Path::new(dir);
                for p in &script.polymorphic {
                    fs::write(dir.join(format!("{}.schematic.goals", p.name)), &p.goals)
                        .map_err(|e| e.to_string())?;
                    fs::write(dir.join(format!("{}.schematic.proof", p.name)), &p.proof)
                        .map_err(|e| e.to_string())?;
                }
            }
            // Results are printed only after the kernel accepted the derivation.
            for e in &script.evaluations {
                println!("{} = {} : {}", e.name, e.value, e.ty);
            }
            for p in &script.polymorphic {
                println!(
                    "ACCEPT (schematic {}): every level L, {} steps, {} inductions",
                    p.name, p.steps, p.inductions
                );
            }
            let report = &script.certified.checked;
            match &script.certified.oracle {
                Some(oracle) => println!(
                    "ACCEPT (cubical script): {} goals, {} proof steps, {} oracle bytes",
                    report.goals,
                    report.steps,
                    oracle.len()
                ),
                None => println!(
                    "ACCEPT (cubical script): {} goals, {} proof steps",
                    report.goals, report.steps
                ),
            }
            let used = &script.certified.rules_used;
            let generated = used.iter().filter(|r| r.contains('/')).count();
            println!(
                "relies on {} of the theory's {} rules ({} generated by declarations and definitions)",
                used.len(),
                cubical::generate::rule_count(&script.certified.theory),
                generated
            );
            if let Some(dir) = output {
                let list: String = used.iter().map(|r| format!("{r}\n")).collect();
                fs::write(std::path::Path::new(dir).join("rules-used"), list)
                    .map_err(|e| e.to_string())?;
            }
        }
        ["generate", name, rest @ ..] => {
            let output = match rest {
                [] => None,
                ["--emit", dir] => Some(*dir),
                _ => return Err(usage.into()),
            };
            if let Some(dir) = output {
                // Refuse before the long generation, not after it.
                if std::path::Path::new(dir).exists() {
                    return Err(format!("{dir} already exists"));
                }
            }
            let generated = cubical::generate::regenerate(name)?;
            if let Some(dir) = output {
                fs::create_dir(dir)
                    .map_err(|e| format!("cannot create new directory {dir}: {e}"))?;
                let dir = std::path::Path::new(dir);
                fs::write(dir.join("goals"), &generated.goals).map_err(|e| e.to_string())?;
                let oracle = generated.oracle.as_deref().ok_or("no oracle")?;
                fs::write(dir.join("proof.oracle"), oracle).map_err(|e| e.to_string())?;
            }
            let bundled = cubical::EXAMPLES.iter().find(|e| e.name == *name);
            println!(
                "ACCEPT (regenerated cubical {name}): {} goals, {} proof steps, {} oracle bytes, {} of {} rules used{}",
                generated.checked.goals,
                generated.checked.steps,
                generated.oracle.as_ref().map_or(0, Vec::len),
                generated.rules_used.len(),
                cubical::generate::rule_count(&generated.theory),
                match bundled {
                    Some(e) if e.goals == generated.goals => ", same goals as the bundled example",
                    Some(_) => ", goals DIFFER from the bundled example",
                    None => "",
                }
            );
        }
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
