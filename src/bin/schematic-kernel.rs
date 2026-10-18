//! Research prototype: check a schematic certificate (see `horn::schematic`),
//! and optionally write a ground instance of it for the ground kernel.
use horn::schematic::{check, export_agda, instantiate};
use std::{
    env,
    fs::{self, File},
    io::{BufReader, BufWriter, Write},
    process, thread,
};

fn run() -> Result<(), String> {
    let mut args: Vec<_> = env::args().collect();
    let agda = if args.get(1).is_some_and(|a| a == "--agda") {
        args.remove(1);
        Some((args.remove(1), args.pop().unwrap_or_default()))
    } else {
        None
    };
    if agda.is_some() && args.len() != 4 {
        return Err("usage: schematic-kernel --agda MODULE THEORY GOALS PROOF OUT.agda".into());
    }
    if args.len() != 4 && args.len() != 7 {
        return Err(
            "usage: schematic-kernel THEORY GOALS PROOF [VAR=TERM OUT_GOALS OUT_PROOF]".into(),
        );
    }
    let theory = fs::read_to_string(&args[1]).map_err(|e| format!("{}: {e}", args[1]))?;
    let goals = fs::read_to_string(&args[2]).map_err(|e| format!("{}: {e}", args[2]))?;
    let input = File::open(&args[3]).map_err(|e| format!("{}: {e}", args[3]))?;
    let input = BufReader::with_capacity(1 << 20, input);
    let r = if let Some((module, path)) = &agda {
        let mut out = File::create(path)
            .map(BufWriter::new)
            .map_err(|e| format!("{path}: {e}"))?;
        let r = export_agda(&theory, &goals, input, module, &mut out)?;
        out.flush().map_err(|e| e.to_string())?;
        r
    } else if let [binding, g, p] = &args[4..] {
        let (v, t) = binding.split_once('=').ok_or("expected VAR=TERM")?;
        let create = |p: &String| {
            File::create(p)
                .map(BufWriter::new)
                .map_err(|e| format!("{p}: {e}"))
        };
        let (mut g, mut p) = (create(g)?, create(p)?);
        let r = instantiate(
            &theory,
            &goals,
            input,
            &[(v.into(), t.into())],
            &mut g,
            &mut p,
        )?;
        g.flush().map_err(|e| e.to_string())?;
        p.flush().map_err(|e| e.to_string())?;
        r
    } else {
        check(&theory, &goals, input)?
    };
    println!(
        "ACCEPT {} goals ({} open), {} steps, {} hypotheses, {} inductions, {} instance references",
        r.goals, r.open_goals, r.steps, r.hypotheses, r.inductions, r.instances
    );
    Ok(())
}

fn main() {
    let result = thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(run)
        .expect("spawn checker thread")
        .join()
        .expect("checker thread panicked");
    if let Err(e) = result {
        println!("REJECT {e}");
        process::exit(1);
    }
}
