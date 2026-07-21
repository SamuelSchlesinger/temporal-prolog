# Testing strategy

The Haskell and Rust implementations are independent engines with matching
language-level coverage. Test counts are not normally a coverage metric:
Hspec reports each `it` example, while Rust tests historically grouped several
behaviors into one function. The Rust suite now also uses fine-grained tests,
so omissions are easier to spot and failures identify one behavior at a time.

| Behavior area | Haskell tests | Rust tests |
|---|---|---|
| Surface syntax, precedence, aliases, pretty-printing, round trips, and rejection boundaries | `test/Main.hs` parser and feature specs | `rust/src/parser.rs`, `rust/src/pretty.rs`, `rust/tests/pretty.rs` |
| AST groundness, variables, substitutions, and symbol signatures | syntax and unification specs | `rust/src/ast.rs`, `rust/src/engine.rs` |
| Five-step normalization and generated-name provenance | normalizer and term-previous specs | `rust/src/normalize.rs` |
| First-order unification and occurs check | unification specs | `rust/src/engine.rs` |
| Fixed-point execution, temporal operators, arithmetic, and pattern functions | interpreter, operator, and backward-chaining specs | `rust/tests/language_semantics.rs`, `rust/tests/operators.rs` |
| Negative cycles and all classical minimal models | stratification and conformance specs | `rust/src/engine.rs`, `rust/tests/conformance.rs` |
| Runtime query and assertion validation | runtime-boundary specs | `rust/src/engine.rs`, `rust/tests/language_semantics.rs` |
| Deterministic batch output | batch specs | `rust/src/batch.rs` |
| Bounded protocol model checking | model-checker specs | `rust/src/model_checker.rs`, `rust/tests/model_checker.rs` |
| Exhaustive two-atom truth-table oracle | propositional-oracle spec | `rust/tests/oracle.rs` |

The shared corpus remains the strongest cross-implementation gate:

```sh
sh conformance/run.sh
```

Run the implementation suites independently with:

```sh
cabal test all
cargo test --manifest-path rust/Cargo.toml --all-targets
```

The repository-level Rust conformance and model-checker tests read shared files
outside `rust/`. They are deliberately omitted from the published crate archive;
the crate retains all self-contained unit, language, operator, and oracle tests,
and CI tests the extracted package as well as the full repository suite.

Implementation-specific APIs are tested in their own suites rather than forced
into a false one-to-one mapping. Haskell additionally exposes warning,
derivation-tracing, and indexed-world APIs; Rust additionally tests its public
AST transformations and standalone package boundary. The shared corpus and the
semantic rows above are the portability contract.
