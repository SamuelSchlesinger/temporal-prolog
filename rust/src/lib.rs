//! A Rust implementation of the Temporal Prolog language specified in
//! `../spec/temporal-prolog.tex`.

pub mod ast;
pub mod batch;
pub mod engine;
pub mod model_checker;
pub mod normalize;
pub mod parser;
pub mod scenario;

pub use ast::*;
pub use batch::*;
pub use engine::*;
pub use model_checker::*;
pub use normalize::*;
pub use parser::*;
pub use scenario::*;

/// Parse and normalize a portable source program, retaining generated-name
/// metadata for user-facing renderers.
pub fn compile(source: &str) -> Result<NormalizedProgram, String> {
    normalize(parser::parse_program(source)?)
}
