use crate::lex::{Kind, Lexer, Token};
use std::fmt;
use std::io::BufRead;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

pub type Result<T> = std::result::Result<T, String>;

pub fn atom(s: impl Into<String>) -> Sexp {
    Sexp::Atom(s.into())
}

pub fn call(name: &str, args: impl IntoIterator<Item = Sexp>) -> Sexp {
    Sexp::List(std::iter::once(atom(name)).chain(args).collect())
}

impl Sexp {
    pub fn atom(&self) -> Result<&str> {
        match self {
            Self::Atom(s) => Ok(s),
            _ => Err(format!("expected atom, got {self}")),
        }
    }

    pub fn list(&self) -> Result<&[Self]> {
        match self {
            Self::List(xs) => Ok(xs),
            _ => Err(format!("expected list, got {self}")),
        }
    }
}

impl fmt::Display for Sexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Atom(s) => write!(f, "{s}"),
            Self::List(xs) => {
                write!(f, "(")?;
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{x}")?;
                }
                write!(f, ")")
            }
        }
    }
}

pub const MAX_DEPTH: usize = 256;

pub fn parse(input: &str) -> Result<Vec<Sexp>> {
    let mut lexer = Lexer::new(input.as_bytes());
    let mut out = Vec::new();
    while lexer.peek()?.is_some() {
        out.push(read(&mut lexer, 0)?);
    }
    Ok(out)
}

/// Read one S-expression whose nesting depth is `depth`.
pub fn read<R: BufRead>(lexer: &mut Lexer<R>, depth: usize) -> Result<Sexp> {
    if depth > MAX_DEPTH {
        return Err("S-expression nesting exceeds 256".into());
    }
    match lexer.token()?.ok_or("unexpected end of input")? {
        Token::Open => {
            let mut xs = Vec::new();
            while lexer.peek()? != Some(Kind::Close) {
                xs.push(read(lexer, depth + 1)?);
            }
            lexer.token()?;
            Ok(Sexp::List(xs))
        }
        Token::Close => Err("unexpected closing parenthesis".into()),
        Token::Atom(word) => Ok(atom(word)),
    }
}
