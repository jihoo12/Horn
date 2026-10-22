//! An in-process pipe that hands over text in large chunks. An OS pipe
//! holds 64 KiB, so streaming a large certificate from one thread to another
//! through it costs a wake-up per 64 KiB on each side; on the cubical
//! scripts that waiting took longer than writing and checking together.

use std::io::{BufRead, Read, Result, Write};
use std::sync::mpsc::{Receiver, SyncSender, sync_channel};

/// Bytes per chunk.
const CHUNK: usize = 1 << 20;
/// Chunks in flight; bounds the memory between writer and reader.
const DEPTH: usize = 4;

/// The writing end. Dropping it ends the reader's input.
pub struct ChunkWriter {
    tx: SyncSender<Vec<u8>>,
    buf: Vec<u8>,
}

/// The reading end. Dropping it makes further writes fail.
pub struct ChunkReader {
    rx: Receiver<Vec<u8>>,
    chunk: Vec<u8>,
    pos: usize,
}

pub fn pipe() -> (ChunkReader, ChunkWriter) {
    let (tx, rx) = sync_channel(DEPTH);
    (
        ChunkReader {
            rx,
            chunk: Vec::new(),
            pos: 0,
        },
        ChunkWriter {
            tx,
            buf: Vec::with_capacity(CHUNK),
        },
    )
}

impl ChunkWriter {
    fn send(&mut self) -> Result<()> {
        if self.buf.is_empty() {
            return Ok(());
        }
        let full = std::mem::replace(&mut self.buf, Vec::with_capacity(CHUNK));
        self.tx
            .send(full)
            .map_err(|_| std::io::ErrorKind::BrokenPipe.into())
    }
}

impl Write for ChunkWriter {
    fn write(&mut self, data: &[u8]) -> Result<usize> {
        self.buf.extend_from_slice(data);
        if self.buf.len() >= CHUNK {
            self.send()?;
        }
        Ok(data.len())
    }
    fn flush(&mut self) -> Result<()> {
        self.send()
    }
}

impl Drop for ChunkWriter {
    fn drop(&mut self) {
        // A reader that has gone away needs nothing more.
        let _ = self.send();
    }
}

impl BufRead for ChunkReader {
    fn fill_buf(&mut self) -> Result<&[u8]> {
        while self.pos == self.chunk.len() {
            match self.rx.recv() {
                Ok(next) => {
                    self.chunk = next;
                    self.pos = 0;
                }
                // The writer is gone: end of input.
                Err(_) => return Ok(&[]),
            }
        }
        Ok(&self.chunk[self.pos..])
    }
    fn consume(&mut self, n: usize) {
        self.pos = (self.pos + n).min(self.chunk.len());
    }
}

impl Read for ChunkReader {
    fn read(&mut self, out: &mut [u8]) -> Result<usize> {
        let available = self.fill_buf()?;
        let n = available.len().min(out.len());
        out[..n].copy_from_slice(&available[..n]);
        self.consume(n);
        Ok(n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn carries_every_byte_in_order() {
        let data: Vec<u8> = (0..3 * CHUNK + 12345).map(|i| (i % 251) as u8).collect();
        let (mut reader, mut writer) = pipe();
        std::thread::scope(|s| {
            s.spawn(|| {
                for piece in data.chunks(7000) {
                    writer.write_all(piece).unwrap();
                }
                drop(writer);
            });
            let mut got = Vec::new();
            reader.read_to_end(&mut got).unwrap();
            assert_eq!(got, data);
        });
    }

    #[test]
    fn writes_fail_once_the_reader_is_gone() {
        let (reader, mut writer) = pipe();
        drop(reader);
        let chunk = vec![0u8; CHUNK];
        let failed = (0..DEPTH + 2).any(|_| writer.write_all(&chunk).is_err());
        assert!(failed);
    }
}
