extern crate combine;
extern crate tokenizer;

use tokenizer::{Keyword, Language, Punctuation};

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Kind {
  Comma,
  Dot,
  LeftParen,
  RightParen,
  SemiColon,

  Select,
  From,
  Where,
}

pub struct Sql {}
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
  fn peek_token(&self, _text: &str) -> Option<(Self::Kind, usize)> {
    None
  }
  fn skip_comments(&self, _text: &str) -> Option<usize> {
    None
  }
}

#[cfg(test)]
mod tests {
  use super::Kind::*;
  use combine::{Positioned, StreamOnce};
  use tokenizer::TokenStream;

  use super::*;
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

  #[test]
  fn basic_tokens() {
    let stream = TokenStream::new(Sql {}, ",.();");
    assert_eq!(
      tok_typ(stream),
      vec![Comma, Dot, LeftParen, RightParen, SemiColon]
    )
  }
}
