//! Research measurement: how well the oracle's adaptive model, trained on
//! other certificates, predicts the proof decisions of a target certificate.
//! usage: horn-predict THEORY TARGET_GOALS TARGET_PROOF [GOALS PROOF]...
use std::fs;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 || (args.len() - 4) % 2 != 0 {
        eprintln!("usage: horn-predict THEORY TARGET_GOALS TARGET_PROOF [GOALS PROOF]...");
        std::process::exit(2);
    }
    let read = |p: &str| fs::read(p).unwrap_or_else(|e| panic!("{p}: {e}"));
    let theory = String::from_utf8(read(&args[1])).unwrap();
    let target_goals = String::from_utf8(read(&args[2])).unwrap();
    let target_proof = read(&args[3]);
    let corpus_data: Vec<(String, Vec<u8>)> = args[4..]
        .chunks(2)
        .map(|c| (String::from_utf8(read(&c[0])).unwrap(), read(&c[1])))
        .collect();
    let corpus: Vec<(&str, &[u8])> = corpus_data.iter().map(|(g, p)| (g.as_str(), p.as_slice())).collect();
    match horn::oracle::prediction_experiment(&theory, &corpus, (&target_goals, &target_proof)) {
        Ok(s) => println!(
            "trained on {} certificates: {} choices, most probable taken {:.1}%, ranks {:?}",
            corpus.len(),
            s.choices,
            100.0 * s.top1 as f64 / s.choices.max(1) as f64,
            s.rank_hist
        ),
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    }
}
