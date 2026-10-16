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
    let mut tokens = Vec::new();
    for line in input.lines() {
        let line = line.split(';').next().unwrap_or("");
        let mut word = String::new();
        for c in line.chars() {
            if c.is_whitespace() || c == '(' || c == ')' {
                if !word.is_empty() {
                    tokens.push(std::mem::take(&mut word));
                }
                if c == '(' || c == ')' {
                    tokens.push(c.to_string());
                }
            } else {
                word.push(c);
            }
        }
        if !word.is_empty() {
            tokens.push(word);
        }
    }
    fn one(tokens: &[String], pos: &mut usize, depth: usize) -> Result<Sexp> {
        if depth > 256 {
            return Err("S-expression nesting exceeds 256".into());
        }
        let token = tokens.get(*pos).ok_or("unexpected end of input")?;
        *pos += 1;
        match token.as_str() {
            "(" => {
                let mut xs = Vec::new();
                while tokens.get(*pos).map(String::as_str) != Some(")") {
                    xs.push(one(tokens, pos, depth + 1)?);
                }
                *pos += 1;
                Ok(Sexp::List(xs))
            }
            ")" => Err("unexpected closing parenthesis".into()),
            _ => Ok(atom(token)),
        }
    }
    let mut pos = 0;
    let mut out = Vec::new();
    while pos < tokens.len() {
        out.push(one(&tokens, &mut pos, 0)?);
    }
    Ok(out)
}
