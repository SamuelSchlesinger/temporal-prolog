# Revision history for temporal-prolog

## 0.1.0.0 -- 2026-03-17

* Initial release implementing Sakuragawa's (1986) Temporal Prolog.
* Core AST with user-facing and normalized representations.
* Megaparsec-based parser supporting both ASCII and Unicode operator syntax.
* Five-step normalization pipeline (paper Section 5.1):
  - Eliminate future-time result operators (always, until, atnext, next).
  - Eliminate past-time condition operators (since, after, for, has-been, once).
  - Lift term-level previous (@) to condition-level.
  - Expand pattern functions.
  - Push negation to atoms and distribute @ into canonical normal form.
* World-by-world stratified least-fixed-point interpreter with negation-as-failure.
* Built-in predicates: =, >, <, >=, <=, at(N), true, false.
* Interactive REPL with commands for loading programs, stepping through worlds,
  asserting facts, querying, and inspecting history.
* Example programs: foot warmer controller, mutual exclusion, process control,
  and temperature monitoring.
