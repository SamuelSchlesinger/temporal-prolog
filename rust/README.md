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
signatures of built-in operations. The interpreter preserves those signatures
across runtime inputs and prior worlds, prevents assertion of internal
relations, and evaluates built-ins through the public query API.
Source `for` counts are likewise retained exactly. Compilation admits the
portable limit of 1,000 repetitions and rejects larger counts before expansion,
so behavior cannot depend on the host's pointer width.
Generated-name counters are also arbitrary precision: a legal source name with
an `_auxN` suffix above machine range remains observable and advances the next
internal suffix exactly instead of overflowing.
Normalization Steps 1, 2, and 4 each allow 1,000 productive rewrite rounds,
inclusively. A program that reaches normal form on round 1,000 is accepted; a
residual target after that round is rejected as a resource error.

```rust
use temporal_prolog::{compile, Interpreter};

# fn main() -> Result<(), String> {
let program = compile("trigger => next fired.")?;
let mut state = Interpreter::new(program);
state.step()?;
# Ok(())
# }
```

Focused parsers and the source pretty-printer preserve the exact AST, including
temporal and arithmetic precedence:

```rust
use temporal_prolog::{parse_rule, pretty_rule};

# fn main() -> Result<(), String> {
let rule = parse_rule("(ready since start) /\\ enabled => next running.")?;
assert_eq!(
    pretty_rule(&rule),
    "(ready since start) /\\ enabled => next running."
);
# Ok(())
# }
```

The repository contains the normative specification, shared cross-language
conformance corpus, command-line tools, and complete documentation.
