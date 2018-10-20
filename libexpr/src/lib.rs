//! `expr` is a simple language. It looks like the following:
//! ```expr
//! B[5][4][3]; C; x;
//! {
//!   B[1][2][2] = C + 4;
//!   while (x < 10) x = x + 1;
//! }
//! ```

extern crate combine;
extern crate tokenizer;

pub mod ast;
pub mod interp;
pub mod ir;
pub mod parser;
