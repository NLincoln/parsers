//! The expr interpreter
//! Expr, as a language is simple enough that it's code can
//! be both interpreted and compiled. This is mostly due
//! to it's wonderful property of only allowing u32's as values
//! :)
//!
//! This interpreter takes a series of instructions and
//! executes them, returning the final set of values.
//!
//! Put simply, the output of the following expr code;
//!
//! ```expr
//! C; Z; { C = Z + 2; }
//! ```
//!
//! Would be a hashmap that looks like the following:
//! ```plaintext
//! { C: 2, Z: 0 }
//! ```
use crate::ast;
use crate::ir;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Debug, PartialEq)]
pub enum Value {
  Simple(u32),
  Indexed(Vec<u32>),
}

/// Errors that occured during execution of the program
#[derive(Debug)]
pub enum Error<'a> {
  /// An instruction was encountered that doesn't make sense semantically.
  /// This is more of a catch-all error, usually a more specific case will
  /// be given
  InvalidInstruction(&'a ir::Instruction),
  /// Attempted to look up a variable as indexed, but it was simple, or vice versa.
  InvalidTypeLookup(&'a ir::Instruction),
  /// Attempted to assign to a constant value
  AssignToConstantValue(&'a ir::Instruction),
}

/// Finds the value of a value in a variable map.
fn lookup_variable(variable_map: &HashMap<String, Value>, addr: Rc<ir::Address>) -> Option<u32> {
  match (*addr).clone() {
    ir::Address::Integer(val) => Some(val),
    ir::Address::Named(name) => match variable_map[name.as_str()] {
      Value::Simple(val) => Some(val),
      Value::Indexed(_) => None,
    },
    ir::Address::Indexed { name, index } => match &variable_map[name.as_str()] {
      Value::Simple(_) => None,
      Value::Indexed(array) => {
        let index = match (*index).clone() {
          ir::Address::Integer(val) => val as usize,
          ir::Address::Named(name) => match variable_map[name.as_str()] {
            Value::Simple(val) => val as usize,
            Value::Indexed(_) => return None,
          },
          ir::Address::Indexed { .. } => return None,
        };
        Some(array[index])
      }
    },
  }
}

fn set_value(variable_map: &mut HashMap<String, Value>, addr: Rc<ir::Address>, value: u32) {
  match (*addr).clone() {
    ir::Address::Named(name) => {
      variable_map.insert(name, Value::Simple(value));
    }
    ir::Address::Integer(_) => return,
    ir::Address::Indexed { name, index } => {
      let index = match (*index).clone() {
        ir::Address::Integer(val) => val as usize,
        ir::Address::Named(name) => match variable_map[name.as_str()] {
          Value::Simple(val) => val as usize,
          Value::Indexed(_) => return,
        },
        ir::Address::Indexed { .. } => return,
      };
      match variable_map.get_mut(name.as_str()) {
        None => unreachable!(),
        Some(Value::Simple(_)) => return,
        Some(Value::Indexed(array)) => array[index / 4] = value,
      };
    }
  };
}

/// Executes a program and produces the result. This constitutes the entire
/// public API of this module. Pass in an [`ir::Program`](../ir/struct.Program.html)
/// and get back the executed version.
pub fn execute<'a>(program: &'a ir::Program) -> Result<HashMap<String, Value>, Error<'a>> {
  let mut variable_map: HashMap<String, Value> = HashMap::new();

  for variable in program.ast.variables.iter() {
    match variable {
      ast::Variable::Simple(name) => {
        variable_map.insert(name.get().into(), Value::Simple(0));
      }
      ast::Variable::Indexed { name, indexes } => {
        let mut vec = Vec::new();
        vec.resize((ir::width_of_index(&indexes[..]) / 4) as usize, 0);
        variable_map.insert(name.get().into(), Value::Indexed(vec));
      }
    };
  }

  for variable in program.generated_variables() {
    variable_map.insert(variable, Value::Simple(0));
  }

  for instruction in program.instructions() {
    match instruction {
      ir::Instruction::Assign(lhs, rhs) => {
        let value = match lookup_variable(&variable_map, (*rhs).clone()) {
          Some(val) => val,
          None => return Err(Error::InvalidInstruction(instruction)),
        };

        set_value(&mut variable_map, (*lhs).clone(), value);
      }
      ir::Instruction::Operation {
        destination,
        operator,
      } => {
        let value = match operator {
          ir::Operator::Add(lhs, rhs) => {
            let lhs = match lookup_variable(&variable_map, (*lhs).clone()) {
              Some(val) => val,
              None => return Err(Error::InvalidInstruction(instruction)),
            };
            let rhs = match lookup_variable(&variable_map, (*rhs).clone()) {
              Some(val) => val,
              None => return Err(Error::InvalidInstruction(instruction)),
            };
            lhs + rhs
          }
          ir::Operator::Multiply(lhs, rhs) => {
            let lhs = match lookup_variable(&variable_map, (*lhs).clone()) {
              Some(val) => val,
              None => return Err(Error::InvalidInstruction(instruction)),
            };
            let rhs = match lookup_variable(&variable_map, (*rhs).clone()) {
              Some(val) => val,
              None => return Err(Error::InvalidInstruction(instruction)),
            };
            lhs * rhs
          }
          _ => unimplemented!(),
        };
        set_value(&mut variable_map, (*destination).clone(), value);
      }
      _ => unimplemented!(),
    }
  }

  Ok(variable_map)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_basic_reassign() {
    let parsed = crate::parser::parse("C; Z; { C = 1; Z = C;}").unwrap().0;
    let program = crate::ir::Program::from_ast(&parsed);
    let executed = execute(&program).unwrap();

    assert_eq!(executed["C"], Value::Simple(1));
    assert_eq!(executed["Z"], Value::Simple(1))
  }
  #[test]
  fn test_simple_array() {
    let parsed = crate::parser::parse("C[3][2]; { C[1][1] = 5; }").unwrap().0;
    let program = crate::ir::Program::from_ast(&parsed);
    eprintln!("{}", program);
    let executed = execute(&program).unwrap();

    eprintln!("{:#?}", executed);

    assert_eq!(executed["C"], Value::Indexed(vec![0, 0, 0, 5, 0, 0]));
  }
}
