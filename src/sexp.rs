use std::fmt;

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

pub fn parse(input: &str) -> Result<Vec<Sexp>> {
    #[derive(Clone, Copy)]
    enum Token<'a> {
        Open,
        Close,
        Atom(&'a str),
    }
    struct Lexer<'a> {
        rest: &'a str,
    }
    impl<'a> Iterator for Lexer<'a> {
        type Item = Token<'a>;

        fn next(&mut self) -> Option<Self::Item> {
            loop {
                let c = self.rest.chars().next()?;
                if c.is_whitespace() {
                    self.rest = &self.rest[c.len_utf8()..];
                } else if c == ';' {
                    self.rest = self.rest.split_once('\n').map_or("", |(_, tail)| tail);
                } else if c == '(' || c == ')' {
                    self.rest = &self.rest[1..];
                    return Some(if c == '(' { Token::Open } else { Token::Close });
                } else {
                    let end = self
                        .rest
                        .find(|c: char| c.is_whitespace() || matches!(c, '(' | ')' | ';'))
                        .unwrap_or(self.rest.len());
                    let word = &self.rest[..end];
                    self.rest = &self.rest[end..];
                    return Some(Token::Atom(word));
                }
            }
        }
    }
    fn one<'a>(tokens: &mut std::iter::Peekable<Lexer<'a>>, depth: usize) -> Result<Sexp> {
        if depth > 256 {
            return Err("S-expression nesting exceeds 256".into());
        }
        match tokens.next().ok_or("unexpected end of input")? {
            Token::Open => {
                let mut xs = Vec::new();
                while !matches!(tokens.peek(), Some(Token::Close)) {
                    xs.push(one(tokens, depth + 1)?);
                }
                tokens.next();
                Ok(Sexp::List(xs))
            }
            Token::Close => Err("unexpected closing parenthesis".into()),
            Token::Atom(word) => Ok(atom(word)),
        }
    }
    let mut tokens = Lexer { rest: input }.peekable();
    let mut out = Vec::new();
    while tokens.peek().is_some() {
        out.push(one(&mut tokens, 0)?);
    }
    Ok(out)
}
