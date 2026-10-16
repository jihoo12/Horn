use horn::replay;
use std::{
    env,
    fs::{self, File, OpenOptions},
    io::BufReader,
    path::PathBuf,
    process,
    time::{Instant, SystemTime, UNIX_EPOCH},
};
struct Scratch(PathBuf);
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}
fn run() -> Result<(), String> {
    let args: Vec<_> = env::args().collect();
    if args.len() != 4 {
        return Err("usage: stream-kernel THEORY GOALS PROOF".into());
    }
    let read = |p: &str| fs::read_to_string(p).map_err(|e| e.to_string());
    let theory = read(&args[1])?;
    let goals = read(&args[2])?;
    let input = File::open(&args[3]).map_err(|e| e.to_string())?;
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| e.to_string())?
        .as_nanos();
    let path = env::temp_dir().join(format!("horn-replay-{}-{stamp}", process::id()));
    let mut file = OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .open(&path)
        .map_err(|e| e.to_string())?;
    let _cleanup = Scratch(path);
    let start = Instant::now();
    let (report, chunks) = replay::check(
        &theory,
        &goals,
        BufReader::new(input),
        &mut file,
        4 * 1024 * 1024,
    )?;
    println!(
        "ACCEPT (streamed): {} goals, {} proof steps, {} chunks, {:?}",
        report.goals,
        report.steps,
        chunks,
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
