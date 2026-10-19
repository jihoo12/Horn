//! Research: model-guided search for derivations of GOALS over THEORY, with
//! the oracle's adaptive model trained on the corpus certificates. Writes
//! the compact certificate found; check it with `kernel`.
//! usage: horn-search THEORY GOALS OUT ATTEMPTS DEPTH [GOALS PROOF]...
use std::fs;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 6 || (args.len() - 6) % 2 != 0 {
        eprintln!("usage: horn-search THEORY GOALS OUT ATTEMPTS DEPTH [GOALS PROOF]...");
        std::process::exit(2);
    }
    let read = |p: &str| fs::read(p).unwrap_or_else(|e| panic!("{p}: {e}"));
    let theory = String::from_utf8(read(&args[1])).unwrap();
    let goals = String::from_utf8(read(&args[2])).unwrap();
    let corpus_data: Vec<(String, Vec<u8>)> = args[6..]
        .chunks(2)
        .map(|c| (String::from_utf8(read(&c[0])).unwrap(), read(&c[1])))
        .collect();
    let corpus: Vec<(&str, &[u8])> =
        corpus_data.iter().map(|(g, p)| (g.as_str(), p.as_slice())).collect();
    let limits = horn::oracle::SearchLimits {
        attempts: args[4].parse().expect("ATTEMPTS"),
        depth: args[5].parse().expect("DEPTH"),
    };
    let start = std::time::Instant::now();
    match horn::oracle::model_search(&theory, &corpus, &goals, limits) {
        Ok((text, stats)) => {
            fs::write(&args[3], text).unwrap();
            println!(
                "FOUND (not checked): {} goals, {} steps, {} attempts, depth {}, {:.2?}",
                stats.goals, stats.steps, stats.choices, stats.depth, start.elapsed()
            );
        }
        Err(e) => {
            println!("NOT FOUND after {:.2?}: {}", start.elapsed(), e.chars().take(300).collect::<String>());
            std::process::exit(1);
        }
    }
}
