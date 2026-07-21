//! A dependency-free Rust implementation of the Temporal Prolog language
//! specified in `../spec/temporal-prolog.tex`.

pub mod ast;
pub mod engine;
pub mod normalize;
pub mod parser;

pub use ast::*;
pub use engine::*;
pub use normalize::*;
pub use parser::*;

/// Parse and normalize a portable source program.
pub fn compile(source: &str) -> Result<NormalizedProgram, String> {
    normalize(parser::parse_program(source)?)
}
