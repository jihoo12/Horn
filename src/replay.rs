//! Compatibility interface for the former chunked replay layer.
//! The kernel now reads certificates incrementally and stores each distinct
//! subterm once, so large proofs are checked directly in a single pass with
//! no scratch admissions, imported facts, or re-serialization to trust.
use crate::kernel::{Report, Theory};
use crate::sexp::Result;
use std::fs::File;
use std::io::{BufRead, Seek, SeekFrom};

/// Check a certificate read incrementally. The scratch file is truncated and
/// otherwise unused; `chunk_bytes` must be positive and no longer limits forms.
/// The returned count is always one: the whole proof is one checked chunk.
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
    scratch.set_len(0).map_err(|e| e.to_string())?;
    scratch
        .seek(SeekFrom::Start(0))
        .map_err(|e| e.to_string())?;
    Ok((Theory::parse(base)?.check_reader(goals, input)?, 1))
}
