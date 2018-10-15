extern crate combine;

use combine::{parser, Parser, Positioned, StreamOnce};

mod tokenizer;

use self::tokenizer::{Keyword, Language, Punctuation, TokenStream};

#[derive(Debug, PartialEq, Clone, Copy)]
enum Kind {
  Comma,
  Dot,
  LeftParen,
  RightParen,
  SemiColon,

  Select,
  From,
  Where,
}

fn tok_typ<'a>(mut s: TokenStream<'a, Sql>) -> Vec<Kind> {
  use combine::easy::Error;
  let mut r = Vec::new();
  loop {
    match s.uncons() {
      Ok(x) => r.push(x.kind),
      Err(ref e) if e == &Error::end_of_input() => break,
      Err(e) => panic!("Parse error at {}: {}", s.position(), e),
    }
  }
  return r;
}

struct Sql {}
impl Language for Sql {
  type Kind = Kind;
  fn keywords() -> Vec<Keyword<Self::Kind>> {
    use self::Kind::*;

    vec![
      ("select", Select, false),
      ("from", From, false),
      ("where", Where, false),
    ].into_iter()
    .map(|key| Keyword::create(key.0, key.1).set_case_sensitive(key.2))
    .collect()
  }
  fn punctuation() -> Vec<Punctuation<Self::Kind>> {
    use self::Kind::*;
    vec![
      (",", Comma),
      (".", Dot),
      ("(", LeftParen),
      (")", RightParen),
      (";", SemiColon),
    ].into_iter()
    .map(|punc| Punctuation::create(punc.0, punc.1))
    .collect()
  }
  fn peek_token(&self, text: &str) -> Option<(Self::Kind, usize)> {
    None
  }
  fn skip_comments(&self, text: &str) -> Option<usize> {
    None
  }
}

fn main() {
  use self::Kind::*;

  let stream = TokenStream::new(Sql {}, ",.();");
  assert_eq!(
    tok_typ(stream),
    vec![Comma, Dot, LeftParen, RightParen, SemiColon]
  )
}
