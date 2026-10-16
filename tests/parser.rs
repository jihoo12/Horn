#[path = "support/legacy_sexp.rs"]
#[allow(dead_code)]
mod legacy;
use horn::sexp::{Sexp, parse};

fn convert(term: legacy::Sexp) -> Sexp {
    match term {
        legacy::Sexp::Atom(a) => Sexp::Atom(a),
        legacy::Sexp::List(xs) => Sexp::List(xs.into_iter().map(convert).collect()),
    }
}
fn compare(source: &str) {
    assert_eq!(
        parse(source),
        legacy::parse(source).map(|xs| xs.into_iter().map(convert).collect()),
        "input: {source:?}"
    );
}

#[test]
fn lexer_and_parser_match_the_extraction_baseline_exhaustively() {
    let alphabet = ['(', ')', 'a', ' ', ';', '\n', '?', '한', '\u{2003}'];
    for len in 0..=5 {
        for mut code in 0..alphabet.len().pow(len) {
            let mut source = String::new();
            for _ in 0..len {
                source.push(alphabet[code % alphabet.len()]);
                code /= alphabet.len();
            }
            compare(&source);
        }
    }
}

#[test]
fn comments_unicode_line_endings_and_depth_boundaries_are_preserved() {
    for source in [
        "αβ;comment\r\n(한\t글)",
        "a;ignored\rb",
        "a\rb",
        ";())\n()",
        "\u{0085}a\u{2028}b",
        "a;comment",
        "(a;ignored\n(b))",
    ] {
        compare(source);
    }
    for depth in [255, 256, 257, 258, 300] {
        compare(&format!("{}x{}", "(".repeat(depth), ")".repeat(depth)));
        compare(&format!("{}{}", "(".repeat(depth), ")".repeat(depth)));
        compare(&"(".repeat(depth));
    }
}
