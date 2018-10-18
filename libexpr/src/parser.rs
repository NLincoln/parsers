use combine::error::Tracked;
use combine::stream::easy::{Error, Errors, Info};
use combine::{satisfy, ConsumedResult, Parser};
use crate::ast::*;
use std::marker::PhantomData;
use tokenizer::{Pos, Token};

pub fn parse<'a>(input: &'a str) -> ParseResult<'a, Program<'a>> {
  let mut tokenstream = TokenStream::new(ExprLang {}, input);
  program(&mut tokenstream)
}

fn program<'a>(input: &mut TokenStream<'a>) -> ParseResult<'a, Program<'a>> {
  use combine::parser;
  use combine::parser::repeat::many1;
  let variables = many1((variable(), token(Kind::SemiColon)).map(|var| var.0));

  let statements = many1((parser(statement), token(Kind::SemiColon)).map(|var| var.0));

  (
    variables,
    token(Kind::LeftBrace),
    statements,
    token(Kind::RightBrace),
  )
    .map(|(variables, _, statements, _)| Program {
      variables,
      body: statements,
    }).parse_stream(input)
}

fn ident<'a>() -> impl Parser<Input = TokenStream<'a>, Output = Ident<'a>> {
  token(Kind::Ident).map(|token| Ident::create(token.value))
}

fn variable<'a>() -> impl Parser<Input = TokenStream<'a>, Output = Variable<'a>> {
  use combine::parser::choice::choice;
  use combine::parser::combinator::attempt;
  use combine::parser::repeat::many1;

  let index = || (token(Kind::LeftBrack), intconst(), token(Kind::RightBrack)).map(|val| val.1);

  choice((
    attempt(
      (ident(), many1(index())).map(|(ident, indexes)| Variable::Indexed {
        name: ident,
        indexes,
      }),
    ),
    ident().map(|ident| Variable::Simple(ident)),
  ))
}

fn intconst<'a>() -> impl Parser<Input = TokenStream<'a>, Output = u32> {
  token(Kind::IntConst).map(|token| token.value.parse().expect("Invalid int constant"))
}

fn statement<'a>(input: &mut TokenStream<'a>) -> ParseResult<'a, Statement<'a>> {
  use combine::parser;
  use combine::parser::choice::{choice, optional};
  let assign = (variable(), token(Kind::EqualSign), expr())
    .map(|(lhs, _, rhs)| Statement::Assign { lhs, rhs });
  let r#while = (
    token(Kind::While),
    token(Kind::LeftParen),
    relative_expr(),
    token(Kind::RightParen),
    parser(statement),
  )
    .map(|(_, _, cond, _, body)| Statement::While {
      cond,
      body: Box::new(body),
    });

  let r#if = (
    token(Kind::If),
    relative_expr(),
    token(Kind::Then),
    parser(statement),
    optional((token(Kind::Else), parser(statement)).map(|else_part| else_part.1)),
  )
    .map(|(_, cond, _, truthey, falsey)| Statement::If {
      cond,
      truthey: Box::new(truthey),
      falsey: falsey.map(Box::new),
    });

  choice((assign, r#while, r#if)).parse_stream(input)
}

fn relative_op<'a>() -> impl Parser<Input = TokenStream<'a>, Output = RelativeOp> {
  use combine::parser::choice::choice;
  choice((
    token(Kind::Lt).map(|_| RelativeOp::Lt),
    token(Kind::Gt).map(|_| RelativeOp::Gt),
    token(Kind::Lte).map(|_| RelativeOp::Lte),
    token(Kind::Gte).map(|_| RelativeOp::Gte),
    token(Kind::Ne).map(|_| RelativeOp::Ne),
    token(Kind::Eq).map(|_| RelativeOp::Eq),
  ))
}

fn relative_expr<'a>() -> impl Parser<Input = TokenStream<'a>, Output = RelativeExpression<'a>> {
  (expr(), relative_op(), expr()).map(|(lhs, op, rhs)| RelativeExpression { op, lhs, rhs })
}

fn expr_variable<'a>(input: &mut TokenStream<'a>) -> ParseResult<'a, ExprVariable<'a>> {
  use combine::parser::choice::choice;
  use combine::parser::combinator::attempt;
  use combine::parser::repeat::many1;

  let index = (token(Kind::LeftBrack), expr(), token(Kind::RightBrack)).map(|(_, expr, _)| expr);

  choice((
    attempt(
      (ident(), many1(index)).map(|(ident, indexes)| ExprVariable::Indexed {
        name: ident,
        indexes,
      }),
    ),
    ident().map(ExprVariable::Simple),
  )).parse_stream(input)
}

fn expr<'a>() -> impl Parser<Input = TokenStream<'a>, Output = Expr<'a>> {
  use combine::parser;
  use combine::parser::choice::choice;
  use combine::parser::combinator::attempt;

  choice((
    attempt(
      (parser(expr_variable), token(Kind::Plus), intconst())
        .map(|(var, _, integer)| Expr::Addition { var, integer }),
    ),
    intconst().map(Expr::IntConst),
    parser(expr_variable).map(Expr::Variable),
  ))
}

pub struct ExprLang {}
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Kind {
  Ident,
  IntConst,
  LeftBrack,
  RightBrack,
  LeftParen,
  RightParen,
  SemiColon,
  Lt,
  Gt,
  Lte,
  Gte,
  Ne,
  Eq,
  Plus,
  EqualSign,
  LeftBrace,
  RightBrace,
  While,
  If,
  Then,
  Else,
}
use tokenizer::{Keyword, Language, Punctuation};
impl Language for ExprLang {
  type Kind = Kind;
  fn keywords() -> Vec<Keyword<Kind>> {
    vec![
      Keyword::create("while", Kind::While),
      Keyword::create("if", Kind::If),
      Keyword::create("then", Kind::Then),
      Keyword::create("else", Kind::Else),
    ]
  }

  fn punctuation() -> Vec<Punctuation<Kind>> {
    vec![
      Punctuation::create("[", Kind::LeftBrack),
      Punctuation::create("]", Kind::RightBrack),
      Punctuation::create("(", Kind::LeftParen),
      Punctuation::create(")", Kind::RightParen),
      Punctuation::create("{", Kind::LeftBrace),
      Punctuation::create("}", Kind::RightBrace),
      Punctuation::create("<=", Kind::Lte),
      Punctuation::create(">=", Kind::Gte),
      Punctuation::create("!=", Kind::Ne),
      Punctuation::create("==", Kind::Eq),
      Punctuation::create("=", Kind::EqualSign),
      Punctuation::create("<", Kind::Lt),
      Punctuation::create(">", Kind::Gt),
      Punctuation::create("+", Kind::Plus),
      Punctuation::create(";", Kind::SemiColon),
    ]
  }

  fn peek_token(&self, text: &str) -> Option<(Kind, usize)> {
    let mut iter = text.char_indices().peekable();

    let cur_char = match iter.next() {
      Some((_, cur_char)) => cur_char,
      None => return None,
    };

    match cur_char {
      'A'...'Z' | 'a'...'z' => {
        let len = loop {
          let (idx, cur_char) = match iter.next() {
            Some(pair) => pair,
            None => break text.len(),
          };
          match cur_char {
            'A'...'Z' | 'a'...'z' => continue,
            _ => break idx,
          }
        };

        return Some((Kind::Ident, len));
      }
      '0'...'9' => {
        let len = loop {
          let (idx, cur_char) = match iter.next() {
            Some(pair) => pair,
            None => break text.len(),
          };
          match cur_char {
            '0'...'9' => continue,
            _ => break idx,
          }
        };

        return Some((Kind::IntConst, len));
      }
      _ => {}
    }
    return None;
  }
}

pub type TokenStream<'a> = tokenizer::TokenStream<'a, ExprLang>;
pub type ParseResult<'a, T> = combine::ParseResult<T, TokenStream<'a>>;

#[derive(Debug, Clone)]
pub struct TokenMatch<'a> {
  kind: Kind,
  phantom: PhantomData<&'a ()>,
}

impl<'a> Parser for TokenMatch<'a> {
  type Input = TokenStream<'a>;
  type Output = Token<'a, Kind>;
  type PartialState = ();

  fn parse_lazy(&mut self, input: &mut Self::Input) -> ConsumedResult<Self::Output, Self::Input> {
    satisfy(|c: Token<'a, Kind>| c.kind == self.kind).parse_lazy(input)
  }

  fn add_error(&mut self, error: &mut Tracked<Errors<Token<'a, Kind>, Token<'a, Kind>, Pos>>) {
    error
      .error
      .add_error(Error::Expected(Info::Owned(format!("{:?}", self.kind))));
  }
}

///
/// Matches a single token coming off of the stream
///
pub fn token<'a>(kind: Kind) -> TokenMatch<'a> {
  TokenMatch {
    kind,
    phantom: PhantomData,
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  pub fn parse_str<'a, T: 'a>(
    mut parser: impl Parser<Input = TokenStream<'a>, Output = T>,
    text: &'a str,
  ) -> Result<
    T,
    combine::easy::Errors<tokenizer::Token<'a, Kind>, tokenizer::Token<'a, Kind>, tokenizer::Pos>,
  > {
    parser
      .parse(TokenStream::new(ExprLang {}, text))
      .map(|result| result.0)
  }

  pub fn parse_good_str<'a, T: 'a>(
    parser: impl Parser<Input = TokenStream<'a>, Output = T>,
    text: &'static str,
  ) -> T {
    match parse_str(parser, text) {
      Ok(res) => res,
      Err(err) => {
        eprintln!(
          "Encountered Error while parsing assumed-to-be-valid string {}",
          text
        );
        eprintln!("{:#?}", err);
        panic!();
      }
    }
  }

  #[test]
  fn test_variables() {
    assert_eq!(
      parse_good_str(variable(), "fOo"),
      Variable::Simple(Ident::create("fOo"))
    );
    assert_eq!(
      parse_good_str(variable(), "foo[1][223][400]"),
      Variable::Indexed {
        name: Ident::create("foo"),
        indexes: vec![1, 223, 400]
      }
    );
  }
  use combine::parser;
  #[test]
  fn test_assign_statement() {
    assert_eq!(
      parse_good_str(parser(statement), "foo = x + 1"),
      Statement::Assign {
        lhs: Variable::Simple(Ident::create("foo")),
        rhs: Expr::Addition {
          var: ExprVariable::Simple(Ident::create("x")),
          integer: 1
        }
      }
    );
  }
  #[test]
  fn test_while_statement() {
    assert_eq!(
      parse_good_str(parser(statement), "while (x < 10) x = x + 1"),
      Statement::While {
        cond: RelativeExpression {
          op: RelativeOp::Lt,
          lhs: Expr::Variable(ExprVariable::Simple(Ident::create("x"))),
          rhs: Expr::IntConst(10)
        },
        body: Box::new(Statement::Assign {
          lhs: Variable::Simple(Ident::create("x")),
          rhs: Expr::Addition {
            var: ExprVariable::Simple(Ident::create("x")),
            integer: 1
          }
        })
      }
    )
  }

  #[test]
  fn test_if_statement() {
    assert_eq!(
      parse_good_str(parser(statement), "if x[1][2] > 5 then x = y + 5"),
      Statement::If {
        cond: RelativeExpression {
          op: RelativeOp::Gt,
          lhs: Expr::Variable(ExprVariable::Indexed {
            name: Ident::create("x"),
            indexes: vec![Expr::IntConst(1), Expr::IntConst(2)]
          }),
          rhs: Expr::IntConst(5)
        },
        truthey: Box::new(Statement::Assign {
          lhs: Variable::Simple(Ident::create("x")),
          rhs: Expr::Addition {
            var: ExprVariable::Simple(Ident::create("y")),
            integer: 5
          }
        }),
        falsey: None
      }
    )
  }

  #[test]
  fn test_if_else_statement() {
    assert_eq!(
      parse_good_str(
        parser(statement),
        "if x[1][2] > 5 then x = y + 5 else x = y + 1"
      ),
      Statement::If {
        cond: RelativeExpression {
          op: RelativeOp::Gt,
          lhs: Expr::Variable(ExprVariable::Indexed {
            name: Ident::create("x"),
            indexes: vec![Expr::IntConst(1), Expr::IntConst(2)]
          }),
          rhs: Expr::IntConst(5)
        },
        truthey: Box::new(Statement::Assign {
          lhs: Variable::Simple(Ident::create("x")),
          rhs: Expr::Addition {
            var: ExprVariable::Simple(Ident::create("y")),
            integer: 5
          }
        }),
        falsey: Some(Box::new(Statement::Assign {
          lhs: Variable::Simple(Ident::create("x")),
          rhs: Expr::Addition {
            var: ExprVariable::Simple(Ident::create("y")),
            integer: 1
          }
        }))
      }
    )
  }

  #[test]
  fn test_whole_program() {
    parse_good_str(
      parser(program),
      "
      x; y; z[1][2][3];
      {
        z[3][2][1] = z[1][1][z[4]];
        y = 15;
        if x < 10 then y = 10 else y = 1;
        while (x < 16) x = x + 2;
      }
      ",
    );
  }
}
