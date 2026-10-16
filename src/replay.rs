//! Generic bounded-memory Horn replay. Each chunk is checked by `kernel`.
//! Only previously verified ground judgments become temporary zero-premise
//! rules; their names are unavailable to the input proof. This module is an
//! additional trusted orchestration layer, containing no object-theory logic.
use crate::kernel::{Report, Theory};
use crate::sexp::{Result, Sexp, parse};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::io::{BufRead, BufWriter, Read, Seek, SeekFrom, Write};

struct Step {
    rule: String,
    refs: Vec<usize>,
    judgment: Sexp,
}
fn index(s: &Sexp) -> Result<usize> {
    s.atom()?
        .parse()
        .map_err(|_| "expected nonnegative index".into())
}
fn io<T>(x: std::io::Result<T>) -> Result<T> {
    x.map_err(|e| e.to_string())
}
struct Replay<'a> {
    base: &'a str,
    rules: BTreeSet<String>,
    prefix: String,
    file: &'a mut File,
    facts: Vec<(u64, usize)>,
    pending: Vec<Step>,
    results: Vec<(String, usize)>,
    bytes: usize,
    chunks: usize,
}
impl Replay<'_> {
    fn fact(&mut self, id: usize) -> Result<String> {
        let (offset, len) = *self.facts.get(id).ok_or("unverified fact reference")?;
        io(self.file.seek(SeekFrom::Start(offset)))?;
        let mut bytes = vec![0; len];
        io(self.file.read_exact(&mut bytes))?;
        String::from_utf8(bytes).map_err(|e| e.to_string())
    }
    fn imports(
        &mut self,
        needed: BTreeSet<usize>,
    ) -> Result<(String, String, BTreeMap<usize, usize>)> {
        let mut theory = self.base.to_owned();
        let mut proof = String::new();
        let mut ids = BTreeMap::new();
        for (local, global) in needed.into_iter().enumerate() {
            let fact = self.fact(global)?;
            let name = format!("{}{}", self.prefix, global);
            theory.push_str(&format!("\n(rule {name} () {fact})\n"));
            proof.push_str(&format!("(step {local} {name} () {fact})\n"));
            ids.insert(global, local);
        }
        Ok((theory, proof, ids))
    }
    fn flush(&mut self) -> Result<()> {
        if self.pending.is_empty() {
            return Ok(());
        }
        let start = self.facts.len();
        let needed = self
            .pending
            .iter()
            .flat_map(|s| s.refs.iter().copied())
            .filter(|n| *n < start)
            .collect();
        let (theory, mut proof, ids) = self.imports(needed)?;
        for (i, step) in self.pending.iter().enumerate() {
            let refs: Vec<_> = step
                .refs
                .iter()
                .map(|n| {
                    if *n < start {
                        ids[n]
                    } else {
                        ids.len() + n - start
                    }
                })
                .map(|n| n.to_string())
                .collect();
            proof.push_str(&format!(
                "(step {} {} ({}) {})\n",
                ids.len() + i,
                step.rule,
                refs.join(" "),
                step.judgment
            ));
        }
        let last = self.pending.last().ok_or("empty chunk")?;
        let goal = format!("(goal replay-chunk {})", last.judgment);
        proof.push_str(&format!(
            "(result replay-chunk {})\n",
            ids.len() + self.pending.len() - 1
        ));
        Theory::parse(&theory)?
            .check(&goal, &proof)
            .map_err(|e| format!("chunk starting at original step {start}: {e}"))?;
        // No pending judgment is admitted until the ENTIRE chunk has passed.
        let mut offset = io(self.file.seek(SeekFrom::End(0)))?;
        let mut writer = BufWriter::new(&mut self.file);
        for step in &self.pending {
            let text = step.judgment.to_string();
            io(writer.write_all(text.as_bytes()))?;
            self.facts.push((offset, text.len()));
            offset += text.len() as u64;
        }
        io(writer.flush())?;
        self.pending.clear();
        self.bytes = 0;
        self.chunks += 1;
        if self.chunks.is_multiple_of(25) {
            eprintln!(
                "CHECKING: {} original steps verified in {} chunks",
                self.facts.len(),
                self.chunks
            );
        }
        Ok(())
    }
    fn form(&mut self, form: Sexp) -> Result<()> {
        let xs = form.list()?;
        match (xs.first().ok_or("empty proof form")?.atom()?, xs.len()) {
            ("step", 5) => {
                let id = index(&xs[1])?;
                if id != self.facts.len() + self.pending.len() {
                    return Err("nonsequential step index".into());
                }
                let rule = xs[2].atom()?.to_owned();
                if !self.rules.contains(&rule) {
                    return Err(format!("unknown source rule {rule}"));
                }
                let refs: Vec<_> = xs[3].list()?.iter().map(index).collect::<Result<_>>()?;
                if refs.iter().any(|n| *n >= id) {
                    return Err("premise is not an earlier step".into());
                }
                self.bytes += form.to_string().len();
                self.pending.push(Step {
                    rule,
                    refs,
                    judgment: xs[4].clone(),
                });
            }
            ("result", 3) => {
                let id = index(&xs[2])?;
                if id >= self.facts.len() + self.pending.len() {
                    return Err("forward result reference".into());
                }
                self.results.push((xs[1].atom()?.to_owned(), id));
            }
            _ => return Err("invalid proof form".into()),
        }
        Ok(())
    }
    fn finish(mut self, goals: &str) -> Result<(Report, usize)> {
        self.flush()?;
        let needed = self.results.iter().map(|(_, id)| *id).collect();
        let (theory, mut proof, ids) = self.imports(needed)?;
        for (name, id) in &self.results {
            proof.push_str(&format!("(result {name} {})\n", ids[id]));
        }
        let final_report = Theory::parse(&theory)?.check(goals, &proof)?;
        Ok((
            Report {
                steps: self.facts.len(),
                goals: final_report.goals,
            },
            self.chunks,
        ))
    }
}

/// Check a certificate using a private scratch file, which is truncated here.
/// Complete forms may span lines; a single form must fit the configured bound.
pub fn check(
    base: &str,
    goals: &str,
    input: impl BufRead,
    scratch: &mut File,
    chunk_bytes: usize,
) -> Result<(Report, usize)> {
    if chunk_bytes == 0 {
        return Err("zero chunk limit".into());
    }
    Theory::parse(base)?;
    let mut rules = BTreeSet::new();
    for f in parse(base)? {
        let xs = f.list()?;
        if xs.first().map(Sexp::atom).transpose()? == Some("rule") {
            rules.insert(xs[1].atom()?.to_owned());
        }
    }
    let mut prefix = "replay-verified-".to_owned();
    while rules.iter().any(|r| r.starts_with(&prefix)) {
        prefix.push('_');
    }
    io(scratch.set_len(0))?;
    io(scratch.seek(SeekFrom::Start(0)))?;
    let mut state = Replay {
        base,
        rules,
        prefix,
        file: scratch,
        facts: vec![],
        pending: vec![],
        results: vec![],
        bytes: 0,
        chunks: 0,
    };
    let mut source = String::new();
    for line in input.lines() {
        source.push_str(&io(line)?);
        source.push('\n');
        if source.len() > chunk_bytes {
            return Err("proof form exceeds chunk byte limit".into());
        }
        let forms = match parse(&source) {
            Ok(forms) => forms,
            Err(e) if e == "unexpected end of input" => continue,
            Err(e) => return Err(e),
        };
        for form in forms {
            state.form(form)?;
            if state.bytes >= chunk_bytes {
                state.flush()?;
            }
        }
        source.clear();
    }
    if !source.is_empty() {
        return Err("incomplete proof form".into());
    }
    state.finish(goals)
}
