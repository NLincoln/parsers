/*!
 * `ir` will take a parsed expr program and transform it into a series of instructions.
 * These instructions can then be executed by the VM or compiled into source code
 */

#[derive(Debug, Clone)]
pub enum Address {
  Named(String),
  Indexed { name: String, index: Rc<Address> },
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
  Label(Rc<Label>),
  /// An instruction to go to a label
  Goto(Rc<Label>),
  /// Add two numbers to something else, looks like a = x + 1
  Operation {
    destination: Rc<Address>,
    operator: Operator,
  },
  If {
    cond: Rc<Address>,
    label: Rc<Label>,
  },
  Assign(Rc<Address>, Rc<Address>),
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

/// An expr program in a form that is ready for
/// optimization, execution, and compilation.
///
/// The program you give is immediately translated
/// upon creating the `Program` struct.
#[derive(Debug)]
pub struct Program<'a> {
  pub ast: &'a ast::Program<'a>,
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

  pub fn generated_variables(&self) -> Vec<String> {
    self
      .addresses
      .iter()
      .filter_map(|val| match (**val).clone() {
        Address::Named(name) => Some(name),
        _ => None,
      }).collect()
  }

  pub fn instructions(&self) -> &[Instruction] {
    self.instructions.as_slice()
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
        let (lhs, mut lhs_inst) = self.expr_variable_ir(lhs);
        let (rhs, mut rhs_inst) = self.expr_ir(rhs);
        lhs_inst.append(&mut rhs_inst);

        lhs_inst.push(Instruction::Assign(lhs, rhs));

        lhs_inst
      }
      ast::Statement::If {
        cond,
        truthey,
        falsey,
      } => {
        let (cond, mut cond_inst) = self.relative_expr_ir(cond);
        let label_a = self.get_label();

        cond_inst.push(Instruction::If {
          cond,
          label: label_a.clone(),
        });
        cond_inst.append(&mut self.statement_ir(truthey));
        match falsey {
          Some(falsey) => {
            let label_b = self.get_label();
            cond_inst.push(Instruction::Goto(label_b.clone()));
            cond_inst.push(Instruction::Label(label_a));
            cond_inst.append(&mut self.statement_ir(falsey));
            cond_inst.push(Instruction::Label(label_b));
          }
          None => {
            cond_inst.push(Instruction::Label(label_a));
          }
        }

        cond_inst
      }
      ast::Statement::While { cond, body } => {
        let top_label = self.get_label();
        let out_label = self.get_label();
        let mut inst = vec![Instruction::Label(top_label.clone())];
        let (cond_addr, mut cond_inst) = self.relative_expr_ir(cond);
        inst.append(&mut cond_inst);
        inst.push(Instruction::If {
          cond: cond_addr,
          label: out_label.clone(),
        });

        inst.append(&mut self.statement_ir(body));
        inst.push(Instruction::Goto(top_label));
        inst.push(Instruction::Label(out_label));

        inst
      }
    }
  }

  fn expr_variable_ir(&mut self, expr: &ast::ExprVariable) -> (Rc<Address>, Vec<Instruction>) {
    match expr {
      ast::ExprVariable::Simple(ident) => (Rc::new(Address::Named(ident.get().into())), vec![]),
      ast::ExprVariable::Indexed { name, indexes } => {
        let indexes: Vec<_> = indexes.iter().map(|index| self.expr_ir(index)).collect();

        let mut result: Vec<Instruction> = Vec::new();
        let ast_info = self
          .ast
          .look_up_variable(name)
          .expect(format!("Unknown variable {}", name.get()).as_str());

        let ast_indexes = match ast_info {
          ast::Variable::Simple(_) => panic!("Cannot index into a non-array"),
          // TODO(2018-10-18): Can we get rid of this clone?
          ast::Variable::Indexed { indexes, .. } => indexes.clone(),
        };

        let mut temp_stack: Vec<Rc<Address>> = Vec::new();

        for (i, (addr, mut instructions)) in indexes.into_iter().enumerate() {
          result.append(&mut instructions);
          let temp = self.get_temp_var();
          temp_stack.push(temp.clone());

          result.push(Instruction::Operation {
            destination: temp,
            operator: Operator::Multiply(
              addr.clone(),
              Rc::new(Address::Integer(width_of_index(&ast_indexes[i + 1..]))),
            ),
          });
        }
        while temp_stack.len() >= 2 {
          // Can unwrap because we know we have two variables.
          let a = temp_stack.pop().unwrap();
          let b = temp_stack.pop().unwrap();
          let temp = self.get_temp_var();

          let inst = Instruction::Operation {
            destination: temp.clone(),
            operator: Operator::Add(b, a),
          };
          temp_stack.push(temp);
          result.push(inst);
        }

        (
          Rc::new(Address::Indexed {
            name: name.get().into(),
            index: temp_stack[0].clone(),
          }),
          result,
        )
      }
    }
  }

  fn expr_ir(&mut self, expr: &ast::Expr) -> (Rc<Address>, Vec<Instruction>) {
    match expr {
      ast::Expr::IntConst(num) => (Rc::new(Address::Integer(*num)), vec![]),
      ast::Expr::Variable(expr_variable) => self.expr_variable_ir(expr_variable),
      ast::Expr::Addition { var, integer } => {
        let temp = self.get_temp_var();
        let (variable, mut instructions) = self.expr_variable_ir(var);
        let inst = Instruction::Operation {
          destination: temp.clone(),
          operator: Operator::Add(variable, Rc::new(Address::Integer(*integer))),
        };
        instructions.push(inst);
        (temp, instructions)
      }
    }
  }

  fn relative_expr_ir(
    &mut self,
    expr: &ast::RelativeExpression,
  ) -> (Rc<Address>, Vec<Instruction>) {
    /*
     * Emit one instruction: the address of the result of the expr
     */
    let (lhs, mut lhs_inst) = self.expr_ir(&expr.lhs);
    let (rhs, mut rhs_inst) = self.expr_ir(&expr.rhs);
    let addr = self.get_temp_var();
    let inst = Instruction::Operation {
      destination: addr.clone(),
      operator: Operator::Relative {
        operands: (lhs, rhs),
        operator: expr.op.clone(),
      },
    };

    // Concat the rhs onto the lhs.
    lhs_inst.append(&mut rhs_inst);
    let mut result_inst = lhs_inst;
    result_inst.push(inst);

    return (addr, result_inst);
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
/// ```plaintext
///      [] -> 4
///      [3, 4] -> 48
///      [10, 3, 4] -> 480
/// ```
pub fn width_of_index(indexes: &[u32]) -> u32 {
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
      Address::Indexed { name, index } => write!(f, "{}[{}]", name, index),
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
      Instruction::Assign(lhs, rhs) => write!(f, "{} = {}", lhs, rhs),
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

  fn assert_program_output(code: &str, expected_output: &str) {
    let parsed = crate::parser::parse(code).unwrap().0;
    let program = Program::from_ast(&parsed);
    let output_code = format!("{}", program);
    if output_code != expected_output {
      eprintln!("Serialized version of program instructions are incorrect.");
      eprintln!("Expected:");
      eprintln!("{}", expected_output);
      eprintln!("But got:");
      eprintln!("{}", output_code);
      panic!();
    }
  }

  #[test]
  fn test_while() {
    assert_program_output(
      "C; { while (C < 10) C = C + 1; }",
      "L1:
t1 = C < 10
if t1 == false goto L2
t2 = C + 1
C = t2
goto L1
L2:
",
    )
  }

  #[test]
  fn test_if() {
    assert_program_output(
      "C; { if C > 0 then C = C + 1; }",
      "t1 = C > 0
if t1 == false goto L1
t2 = C + 1
C = t2
L1:
",
    )
  }

  #[test]
  fn test_if_else() {
    assert_program_output(
      "C; { if C > 0 then C = C + 1 else C = C + 2; }",
      "t1 = C > 0
if t1 == false goto L1
t2 = C + 1
C = t2
goto L2
L1:
t3 = C + 2
C = t3
L2:
",
    );
  }

  #[test]
  fn test_variable_index() {
    assert_program_output(
      "C[4][10][3]; { C[2][5][1] = 7; }",
      "t1 = 2 * 120
t2 = 5 * 12
t3 = 1 * 4
t4 = t2 + t3
t5 = t1 + t4
C[t5] = 7
",
    );
  }
}
