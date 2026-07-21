# Temporal Prolog for Rust

This crate is the independent Rust implementation of Sakuragawa's Temporal
Prolog language in the
[temporal-prolog repository](https://github.com/SamuelSchlesinger/temporal-prolog).
It provides parsing, normalization, branch-preserving execution, pattern
functions, deterministic batch execution, and bounded protocol model checking.
Its integer extension uses arbitrary-precision values and the same signed
floor-division semantics as the Haskell implementation. Compilation validates
the paper's fixed symbol signatures before normalization, including the
input/output arity relationship for pattern functions and the reserved
signatures of built-in operations.

```rust
use temporal_prolog::{compile, Interpreter};

# fn main() -> Result<(), String> {
let program = compile("trigger => next fired.")?;
let mut state = Interpreter::new(program);
state.step()?;
# Ok(())
# }
```

The repository contains the normative specification, shared cross-language
conformance corpus, command-line tools, and complete documentation.
