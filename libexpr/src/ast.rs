//! Structs and enums comprising the AST of expr

use std::fmt::{self, Display};

/// The root-level type. After parsing a program, this
/// is the type that is returned
///
/// The `variables` field can be used to look up any types that might be found
/// in the program. Check out the `lookup_variable` method.
#[derive(Debug, PartialEq)]
pub struct Program<'a> {
  pub variables: Vec<Variable<'a>>,
  pub body: Vec<Statement<'a>>,
}

impl<'a> Program<'a> {
  pub fn look_up_variable(&self, name: &Ident) -> Option<&Variable<'a>> {
    self.variables.iter().find(|var| match var {
      Variable::Simple(ref ident) => ident == name,
      Variable::Indexed {
        name: ref ident, ..
      } => ident == name,
    })
  }
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

impl<'a> Display for Ident<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.0)
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

#[cfg(test)]
mod tests {
  use super::*;
  #[test]
  fn test_lookup_variable() {
    let input = "
        x; y[1]; z[2][3];
        { x = x + 1; }";
    let parsed = crate::parser::parse(input).unwrap().0;
    assert_eq!(
      parsed.look_up_variable(&Ident::create("z")),
      Some(&Variable::Indexed {
        name: Ident::create("z"),
        indexes: vec![2, 3]
      })
    );
    assert_eq!(
      parsed.look_up_variable(&Ident::create("x")),
      Some(&Variable::Simple(Ident::create("x")))
    );
    assert_eq!(parsed.look_up_variable(&Ident::create("not_there")), None);
  }

}
