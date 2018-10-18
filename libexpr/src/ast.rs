#[derive(Debug, PartialEq)]
pub struct Program<'a> {
  pub variables: Vec<Variable<'a>>,
  pub body: Vec<Statement<'a>>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Ident<'a>(&'a str);

impl<'a> Ident<'a> {
  pub fn create(text: &'a str) -> Self {
    Ident(text)
  }
  pub fn get(&self) -> &str {
    self.0
  }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Variable<'a> {
  Simple(Ident<'a>),
  Indexed { name: Ident<'a>, indexes: Vec<u32> },
}

#[derive(Debug, PartialEq, Clone)]
pub enum Statement<'a> {
  Assign {
    lhs: ExprVariable<'a>,
    rhs: Expr<'a>,
  },
  While {
    cond: RelativeExpression<'a>,
    body: Box<Statement<'a>>,
  },
  If {
    cond: RelativeExpression<'a>,
    truthey: Box<Statement<'a>>,
    falsey: Option<Box<Statement<'a>>>,
  },
}

#[derive(Debug, PartialEq, Clone)]
pub enum RelativeOp {
  Lt,
  Gt,
  Lte,
  Gte,
  Ne,
  Eq,
}

use std::fmt::Display;
impl Display for RelativeOp {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    use self::RelativeOp::*;
    write!(
      f,
      "{}",
      match self {
        Lt => "<",
        Gt => ">",
        Lte => "<=",
        Gte => ">=",
        Ne => "!=",
        Eq => "==",
      }
    )
  }
}

#[derive(Debug, PartialEq, Clone)]
pub struct RelativeExpression<'a> {
  pub op: RelativeOp,
  pub lhs: Expr<'a>,
  pub rhs: Expr<'a>,
}

#[derive(Debug, PartialEq, Clone)]
pub enum ExprVariable<'a> {
  Simple(Ident<'a>),
  Indexed {
    name: Ident<'a>,
    indexes: Vec<Expr<'a>>,
  },
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr<'a> {
  IntConst(u32),
  Variable(ExprVariable<'a>),
  Addition { var: ExprVariable<'a>, integer: u32 },
}
