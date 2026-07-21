# Revision history for temporal-prolog

## Unreleased

* Align normalization and world-zero semantics with Sakuragawa's Section 5
  transformations, including the distinct meanings of `~@p` and `@~p`.
* Correct the paper's inconsistent `after` recurrence to implement its strict
  prose semantics, and use exact auxiliary-variable sets.
* Expand term-level previous values at the pattern-function occurrence, and
  support conditional pattern-function reductions.
* Reject non-positive `for` counts and avoid collisions with generated names.
* Implement finite SCC-ordered classical minimal-model enumeration and expose
  all branches through `stepWorldAll`; retain the stratified fast path.
* Identify and specify the overlooked third minimal model in paper Section 4.7.
* Report pattern-function recursion exhaustion as a resource error and enforce
  the executable profile's term-level previous and range restrictions.
* Add an independent Rust parser, normalizer, backward chainer, and world
  evaluator, plus a shared cross-language conformance corpus.
* Add matched, digest-checked Haskell/Rust benchmark harnesses and a normative
  LaTeX specification with paper errata.
* Add matching Haskell and Rust bounded protocol model checkers with a portable
  scenario format, invariant checking, shortest counterexample traces, and
  deterministic Graphviz trees.
* Add a safe nondeterministic arbiter and safe/buggy atomic-commit examples.
* Scope successful model-checking results as `BOUNDED_SAFE`, add independent
  named environment-choice groups (including explicit no-input alternatives),
  and exhaust all four valid two-participant vote combinations.
* Make invariants match stored world facts only, not backward-chained
  pattern-function queries.
* Cross-check each general evaluator against an independent exhaustive oracle
  over 1,024 generated two-atom programs.
* Add matching deterministic Haskell and Rust batch runners with complete
  branch histories, strict schedule validation, and full-state digests.
* Add a byte-for-byte differential conformance gate spanning all temporal
  operator families, pattern functions, arithmetic, negative cycles, and
  shared rejection cases; run both engines, Clippy, and rustfmt in CI.
* Track generated predicates as normalization metadata instead of inferring
  them from `_auxN` spelling, preserving user predicates with similar names in
  REPL, batch, model-checker, and graph output; align fresh-name allocation
  across both engines under source-name collisions.
* Define portable arbitrary-precision integer semantics in both engines,
  including canonical decimal spellings, infix `div`/`mod`, floor division for
  signed operands, and built-in failure for invalid arithmetic.
* Validate fixed predicate, constructor, pattern-function, built-in, and
  arithmetic signatures before normalization; reject built-ins in rule results
  and external assertion streams in both implementations.
* Enforce symbol signatures across runtime assertions and prior worlds, block
  injection of pattern-function relations and generated predicates, and make
  public queries evaluate external predicates with bindings in both engines.
* Add public single-term, condition, result, and rule parsers plus a complete
  source-syntax pretty-printer to the Rust crate; enforce parse/print round trips
  in both implementations and preserve top-level temporal-condition scope.
* Make temporal precedence unambiguous: conjunction binds before
  non-associative `until` and `atnext`, while `since`, `after`, and `for` are
  likewise non-associative; align both parsers and enforce the result rule
  through differential execution.

## 0.1.0.0 -- 2026-03-18

* Initial release implementing Sakuragawa's (1986) Temporal Prolog.
* Core AST with user-facing and normalized representations.
* Megaparsec-based parser supporting both ASCII and Unicode operator syntax.
* Five-step normalization pipeline (paper Section 5.1):
  - Eliminate future-time result operators (always, until, atnext, next).
  - Eliminate past-time condition operators (since, after, for, has-been, once).
  - Lift term-level previous (@) to condition-level.
  - Expand pattern functions into predicate clauses.
  - Push negation to atoms and distribute @ into canonical normal form.
* Normalizer is pure (State + ExceptT) with structured error reporting.
* World-by-world stratified least-fixed-point interpreter with negation-as-failure.
* Backward chaining (SLD-resolution) for pattern-function predicates, supporting
  recursive definitions (e.g. list append) with alpha-renaming and depth limiting.
* Built-in predicates: =, >, <, >=, <=, at(N), true, false.
* Interactive REPL with commands for loading programs, stepping through worlds,
  asserting facts, querying (including pattern-function predicates), tracing
  derivations, and inspecting history.
* Example programs: foot warmer controller, list append, mutual exclusion,
  traffic light state machine, process control, and temperature monitoring.
* 80 tests covering parsing, normalization, interpretation, unification,
  pattern functions, stratification, and edge cases.
