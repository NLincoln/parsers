extern crate combine;
extern crate tokenizer;

pub mod ast;
/**
 * `expr` is a simple language. It looks like the following:
 * ```expr
 * var B[5][4][3]; C; x;
 * {
 *   B[1][2][2] = C + 4;
 *   while (x < 10) x = x + 1;
 * }
 * ```
 */
pub mod parser;

/**
 * `ir` will take a parsed expr program and transform it into a series of instructions.
 * These instructions can then be executed by the VM or compiled into source code
 */
pub mod ir {
  #[derive(Debug)]
  pub enum Address {
    Named(String),
    Integer(u32),
  }

  #[derive(Debug)]
  pub struct Label(u32);
  impl Label {
    pub fn create(val: u32) -> Label {
      Label(val)
    }
    pub fn get_number(&self) -> u32 {
      self.0
    }
  }

  #[derive(Debug)]
  pub struct Index {
    pub ident: String,
    pub index: Rc<Address>,
  }

  #[derive(Debug)]
  pub enum Operator {
    Add(Rc<Address>, Rc<Address>),
    Multiply(Rc<Address>, Rc<Address>),
    Relative {
      operands: (Rc<Address>, Rc<Address>),
      operator: ast::RelativeOp,
    },
  }

  #[derive(Debug)]
  pub enum Instruction {
    /// A label in the output code
    Label(Label),
    /// An instruction to go to a label
    Goto(Label),
    /// Add two numbers to something else, looks like a = x + 1
    Operation {
      destination: Rc<Address>,
      operator: Operator,
    },
    If {
      cond: Rc<Address>,
      label: Label,
    },
    AssignToArray {
      array: Index,
      value: Rc<Address>,
    },
    AssignFromArray {
      array: Index,
      value: Rc<Address>,
    },
  }

  use crate::ast;
  use std::rc::Rc;

  #[derive(Debug)]
  struct Counter(u32);
  impl Counter {
    pub fn new() -> Counter {
      Counter(0)
    }
    pub fn next(&mut self) -> u32 {
      self.0 += 1;
      return self.0;
    }
  }

  #[derive(Debug)]
  pub struct Program<'a> {
    ast: &'a ast::Program<'a>,
    labels: Vec<Rc<Label>>,
    addresses: Vec<Rc<Address>>,
    instructions: Vec<Instruction>,

    label_counter: Counter,
    temp_var_counter: Counter,
  }

  impl<'a> Program<'a> {
    pub fn from_ast(ast: &'a ast::Program<'a>) -> Program<'a> {
      let mut program = Program {
        ast,
        labels: vec![],
        addresses: vec![],
        instructions: vec![],

        label_counter: Counter::new(),
        temp_var_counter: Counter::new(),
      };

      let instructions = program.program_ir(ast);
      program.instructions = instructions;
      program
    }

    fn look_up_variable(&self, name: &ast::Ident) -> Option<&ast::Variable> {
      self.ast.variables.iter().find(|var| match var {
        ast::Variable::Simple(ref ident) => ident == name,
        ast::Variable::Indexed {
          name: ref ident, ..
        } => ident == name,
      })
    }

    fn program_ir(&mut self, program: &ast::Program) -> Vec<Instruction> {
      let mut result = Vec::new();
      for stmt in program.body.iter() {
        result.append(&mut self.statement_ir(&stmt));
      }
      return result;
    }

    fn statement_ir(&mut self, statement: &ast::Statement) -> Vec<Instruction> {
      match statement {
        ast::Statement::Assign { lhs, rhs } => {
          let (lhs, lhs_inst) = self.expr_variable_ir(lhs);
          lhs_inst
        }
        _ => unimplemented!(),
      }
    }

    fn expr_variable_ir(&mut self, expr: &ast::ExprVariable) -> (Rc<Address>, Vec<Instruction>) {
      match expr {
        ast::ExprVariable::Simple(ident) => (Rc::new(Address::Named(ident.get().into())), vec![]),
        ast::ExprVariable::Indexed { name, indexes } => {
          let indexes: Vec<_> = indexes.iter().map(|index| self.expr_ir(index)).collect();

          let mut result: Vec<Instruction> = Vec::new();
          let ast_info = self
            .look_up_variable(name)
            .expect(format!("Unknown variable {}", name.get()).as_str());

          let ast_indexes = match ast_info {
            ast::Variable::Simple(_) => panic!("Cannot index into a non-array"),
            // TODO(2018-10-18): Can we get rid of this clone?
            ast::Variable::Indexed { indexes, .. } => indexes.clone(),
          };

          for (i, (addr, mut instructions)) in indexes.into_iter().enumerate() {
            result.append(&mut instructions);
            let temp = self.get_temp_var();

            result.push(Instruction::Operation {
              destination: temp,
              operator: Operator::Multiply(
                addr.clone(),
                Rc::new(Address::Integer(width_of_index(&ast_indexes[i..]))),
              ),
            })
          }

          (Rc::new(Address::Named("TODO".into())), result)
        }
      }
    }

    fn expr_ir(&mut self, expr: &ast::Expr) -> (Rc<Address>, Vec<Instruction>) {
      match expr {
        ast::Expr::IntConst(num) => (Rc::new(Address::Integer(*num)), vec![]),
        ast::Expr::Variable(expr_variable) => unimplemented!(),
        _ => unimplemented!(),
      }
    }

    fn relative_expr_ir(&mut self, expr: &ast::RelativeExpression) -> Vec<Instruction> {
      /*
       * Emit one instruction: the address of the result of the expr
       */
      let (lhs, mut lhs_inst) = self.expr_ir(&expr.lhs);
      let (rhs, mut rhs_inst) = self.expr_ir(&expr.rhs);

      let inst = Instruction::Operation {
        destination: self.get_temp_var(),
        operator: Operator::Relative {
          operands: (lhs, rhs),
          operator: expr.op.clone(),
        },
      };

      // Concat the rhs onto the lhs.
      lhs_inst.append(&mut rhs_inst);
      let mut result_inst = lhs_inst;
      result_inst.push(inst);

      return result_inst;
    }

    fn get_label(&mut self) -> Rc<Label> {
      let label = Rc::new(Label::create(self.label_counter.next()));
      self.labels.push(label.clone());
      return label;
    }
    fn get_temp_var(&mut self) -> Rc<Address> {
      let addr = Rc::new(Address::Named(format!("t{}", self.temp_var_counter.next())));
      self.addresses.push(addr.clone());
      return addr;
    }
  }

  /// Returns the amount that an array of this type
  /// should be multiplied to get the final index.
  /// E.g.
  ///      [] -> 4
  ///      [3, 4] -> 48
  ///      [10, 3, 4] -> 480
  fn width_of_index(indexes: &[u32]) -> u32 {
    if indexes.len() == 0 {
      4
    } else {
      indexes[0] * width_of_index(indexes.get(1..).unwrap_or(&[]))
    }
  }

  #[test]
  fn test_width_of_index() {
    assert_eq!(width_of_index(&[]), 4);
    assert_eq!(width_of_index(&[3]), 12);
    assert_eq!(width_of_index(&[3, 4]), 48);
    assert_eq!(width_of_index(&[3, 4, 10]), 480);
  }

  use std::fmt::Display;

  impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
      write!(f, "L{}", self.0)
    }
  }

  impl Display for Address {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
      match self {
        Address::Named(ident) => write!(f, "{}", ident),
        Address::Integer(num) => write!(f, "{}", num),
      }
    }
  }

  impl Display for Index {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
      write!(f, "{}[{}]", self.ident, self.index)
    }
  }

  impl Display for Operator {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
      match self {
        Operator::Add(lhs, rhs) => write!(f, "{} + {}", lhs, rhs),
        Operator::Multiply(lhs, rhs) => write!(f, "{} * {}", lhs, rhs),
        Operator::Relative { operands, operator } => {
          write!(f, "{} {} {}", operands.0, operator, operands.1)
        }
      }
    }
  }

  impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
      match self {
        Instruction::AssignFromArray { array, value } => write!(f, "{} = {}", array, value),
        Instruction::AssignToArray { array, value } => write!(f, "{} = {}", value, array),
        Instruction::Goto(dest) => write!(f, "goto {}", dest),
        Instruction::Label(name) => write!(f, "{}:", name),
        Instruction::If { cond, label } => write!(f, "if {} == false goto {}", cond, label),
        Instruction::Operation {
          destination,
          operator,
        } => write!(f, "{} = {}", destination, operator),
      }
    }
  }

  impl<'a> Display for Program<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
      for inst in self.instructions.iter() {
        writeln!(f, "{}", inst)?;
      }
      Ok(())
    }
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
      let program = Program::from_ast(&parsed);
      assert_eq!(
        program.look_up_variable(&ast::Ident::create("z")),
        Some(&ast::Variable::Indexed {
          name: ast::Ident::create("z"),
          indexes: vec![2, 3]
        })
      );
      assert_eq!(
        program.look_up_variable(&ast::Ident::create("x")),
        Some(&ast::Variable::Simple(ast::Ident::create("x")))
      );
      assert_eq!(
        program.look_up_variable(&ast::Ident::create("not_there")),
        None
      );
    }

    #[test]
    fn test_variable_index() {
      let input = "C[4][10][3]; { C[2][5][1] = 7; }";
      let parsed = crate::parser::parse(input).unwrap().0;
      let program = Program::from_ast(&parsed);
      assert_eq!(
        format!("{}", program),
        "t1 = 2 * 120
t2 = 5 * 12
t3 = t1 + t2
t4 = 1 * 4
t5 = t3 + t4
C[t5] = 7"
      )
    }
  }

}
