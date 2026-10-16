//! Streaming S-expression lexer, shared by every parser in the crate.
//! Input is read one line at a time; tokens never span lines because newline
//! is whitespace and comments end at a newline. Atom text is borrowed from the
//! current line, so the borrow checker prevents using it after a refill.
use crate::sexp::Result;
use std::io::BufRead;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Open,
    Close,
    Atom,
}

pub enum Token<'a> {
    Open,
    Close,
    Atom(&'a str),
}

pub struct Lexer<R> {
    input: R,
    line: String,
    pos: usize,
    ahead: Option<Option<(Kind, usize, usize)>>,
    bytes: u64,
}

impl<R: BufRead> Lexer<R> {
    pub fn new(input: R) -> Self {
        Self {
            input,
            line: String::new(),
            pos: 0,
            ahead: None,
            bytes: 0,
        }
    }

    /// Bytes read from the input so far.
    pub fn bytes(&self) -> u64 {
        self.bytes
    }

    fn scan(&mut self) -> Result<Option<(Kind, usize, usize)>> {
        loop {
            let start = self.pos;
            let Some(c) = self.line[start..].chars().next() else {
                self.line.clear();
                self.pos = 0;
                let n = self
                    .input
                    .read_line(&mut self.line)
                    .map_err(|e| e.to_string())?;
                if n == 0 {
                    return Ok(None);
                }
                self.bytes += n as u64;
                continue;
            };
            if c.is_whitespace() {
                self.pos += c.len_utf8();
            } else if c == ';' {
                self.pos = self.line.len();
            } else if c == '(' || c == ')' {
                self.pos += 1;
                let kind = if c == '(' { Kind::Open } else { Kind::Close };
                return Ok(Some((kind, start, start + 1)));
            } else {
                let rest = &self.line[start..];
                let len = rest
                    .find(|c: char| c.is_whitespace() || matches!(c, '(' | ')' | ';'))
                    .unwrap_or(rest.len());
                self.pos = start + len;
                return Ok(Some((Kind::Atom, start, start + len)));
            }
        }
    }

    pub fn peek(&mut self) -> Result<Option<Kind>> {
        if self.ahead.is_none() {
            self.ahead = Some(self.scan()?);
        }
        Ok(self.ahead.flatten().map(|(kind, _, _)| kind))
    }

    pub fn token(&mut self) -> Result<Option<Token<'_>>> {
        let token = match self.ahead.take() {
            Some(token) => token,
            None => self.scan()?,
        };
        Ok(token.map(|(kind, start, end)| match kind {
            Kind::Open => Token::Open,
            Kind::Close => Token::Close,
            Kind::Atom => Token::Atom(&self.line[start..end]),
        }))
    }
}
