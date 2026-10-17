//! Untrusted research tool: report how much of a certificate one schematic
//! derivation covers and what each goal's proof establishes in general, and
//! optionally write the generalized goals and a schematic certificate.
use horn::generalize::generalize;
use std::{
    env,
    fs::{self, File},
    io::{BufReader, BufWriter, Write},
    process,
};

fn run() -> Result<(), String> {
    let args: Vec<_> = env::args().collect();
    if args.len() != 5 && args.len() != 8 {
        return Err(
            "usage: horn-generalize THEORY GOALS PROOF CUT,... [CTOR:POSITION|- OUT_GOALS OUT_PROOF]".into(),
        );
    }
    let read = |p: &String| fs::read_to_string(p).map_err(|e| format!("{p}: {e}"));
    let theory = read(&args[1])?;
    let goals = read(&args[2])?;
    let input = File::open(&args[3]).map_err(|e| format!("{}: {e}", args[3]))?;
    let cut: Vec<&str> = args[4].split(',').filter(|c| !c.is_empty()).collect();
    let create = |p: &String| {
        File::create(p)
            .map(BufWriter::new)
            .map_err(|e| format!("{p}: {e}"))
    };
    let abstract_at = args.get(5).filter(|a| *a != "-").map(String::as_str);
    let mut files = match args.get(6..8) {
        Some([g, p]) => Some((create(g)?, create(p)?)),
        _ => None,
    };
    let out = files
        .as_mut()
        .map(|(g, p)| (g as &mut (dyn Write + Send), p as &mut (dyn Write + Send)));
    let input = BufReader::with_capacity(1 << 20, input);
    let (s, emitted) = generalize(&theory, &goals, input, &cut, abstract_at, out)?;
    if let Some((g, p)) = files.as_mut() {
        g.flush().map_err(|e| e.to_string())?;
        p.flush().map_err(|e| e.to_string())?;
    }
    println!("steps          {}", s.steps);
    println!("skeletons      {}", s.classes);
    println!("ground nodes   {}", s.ground_nodes);
    println!("pattern nodes  {}", s.pattern_nodes);
    println!("class vars     {} ({} flexible)", s.class_vars, s.flex_vars);
    println!("fixed vars     {}", s.fixed_vars);
    println!(
        "subst entries  {} ({} renamings)",
        s.subst_entries, s.subst_renamings
    );
    let h = s.instance_histogram;
    println!(
        "instances      1:{} 2-9:{} 10-99:{} 100+:{}",
        h[0], h[1], h[2], h[3]
    );
    for g in &s.goals {
        println!("goal {}: {} variables", g.name, g.vars.len());
        println!("  general: {}", g.general);
        for (var, flex, value) in g.vars.iter().take(12) {
            let kind = if *flex { "flexible" } else { "rigid" };
            println!("  {var} = {value} ({kind})");
        }
    }
    if let Some(e) = emitted {
        eprintln!(
            "GENERATED (not checked): {} open goals, {} steps, {} inductions, {} definitions; ground: {:?}",
            e.open_goals, e.steps, e.inductions, e.definitions, e.rigid_goals
        );
    }
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("ERROR: {e}");
        process::exit(1);
    }
}
