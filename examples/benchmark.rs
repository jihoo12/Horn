//! End-to-end checking benchmark. Every sample runs in a fresh child process.
use horn::{kernel::Theory, replay};
use std::{
    env,
    fs::{self, File, OpenOptions},
    io::BufReader,
    path::PathBuf,
    process::{self, Command},
    time::{Instant, SystemTime, UNIX_EPOCH},
};

struct Scratch(PathBuf);
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}
fn worker(args: &[String]) -> Result<(), String> {
    let start = Instant::now();
    let read = |p: &str| fs::read_to_string(p).map_err(|e| format!("{p}: {e}"));
    let (steps, goals) = {
        let theory = read(&args[1])?;
        let goals = read(&args[2])?;
        let report = match args[0].as_str() {
            "ordinary" => Theory::parse(&theory)?.check(&goals, &read(&args[3])?)?,
            "streamed" => {
                let stamp = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .map_err(|e| e.to_string())?
                    .as_nanos();
                let path = env::temp_dir().join(format!("horn-bench-{}-{stamp}", process::id()));
                let mut file = OpenOptions::new()
                    .read(true)
                    .write(true)
                    .create_new(true)
                    .open(&path)
                    .map_err(|e| e.to_string())?;
                let _cleanup = Scratch(path);
                let input = File::open(&args[3]).map_err(|e| e.to_string())?;
                replay::check(
                    &theory,
                    &goals,
                    BufReader::new(input),
                    &mut file,
                    4 * 1024 * 1024,
                )?
                .0
            }
            _ => return Err("unknown mode".into()),
        };
        (report.steps, report.goals)
    };
    let elapsed = start.elapsed().as_secs_f64();
    let rss = fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("VmHWM:"))
                .and_then(|l| l.split_whitespace().nth(1))
                .map(str::to_owned)
        })
        .unwrap_or_default();
    println!("{elapsed:.6},{rss},{steps},{goals}");
    Ok(())
}
fn run() -> Result<(), String> {
    let args: Vec<_> = env::args().skip(1).collect();
    if args.first().is_some_and(|a| a == "--worker") && args.len() == 5 {
        return worker(&args[1..]);
    }
    if !(3..=4).contains(&args.len()) {
        return Err("usage: benchmark THEORY GOALS PROOF [RUNS=5]".into());
    }
    let runs: usize = args.get(3).map_or(Ok(5), |s| {
        s.parse().map_err(|_| "invalid run count".to_string())
    })?;
    if runs == 0 {
        return Err("run count must be positive".into());
    }
    let executable = env::current_exe().map_err(|e| e.to_string())?;
    println!("mode,run,seconds,peak_rss_kib,steps,goals");
    for sample in 0..runs {
        // Alternate ordering to avoid always giving one mode the warmer cache.
        let modes = if sample % 2 == 0 {
            ["ordinary", "streamed"]
        } else {
            ["streamed", "ordinary"]
        };
        for mode in modes {
            let output = Command::new(&executable)
                .args(["--worker", mode, &args[0], &args[1], &args[2]])
                .output()
                .map_err(|e| e.to_string())?;
            if !output.status.success() {
                return Err(String::from_utf8_lossy(&output.stderr).into_owned());
            }
            let row = String::from_utf8(output.stdout).map_err(|e| e.to_string())?;
            println!("{mode},{},{}", sample + 1, row.trim());
        }
    }
    Ok(())
}
fn main() {
    if let Err(e) = run() {
        eprintln!("benchmark failed: {e}");
        process::exit(1);
    }
}
