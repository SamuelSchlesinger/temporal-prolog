# Temporal Prolog for Rust

This crate is the independent Rust implementation of Sakuragawa's Temporal
Prolog language in the
[temporal-prolog repository](https://github.com/SamuelSchlesinger/temporal-prolog).
It provides parsing, normalization, branch-preserving execution, pattern
functions, deterministic batch execution, and bounded protocol model checking.

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
