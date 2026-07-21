# Shared conformance corpus

Every `.tpl` file in `cases/` is parsed and executed by both implementations;
every file in `rejections/` must fail parsing, normalization, or executable-
profile validation at the documented boundary.
The Haskell suite in `test/Main.hs` and the Rust integration suite in
`rust/tests/conformance.rs` assert the same semantic outcomes. Internal fresh
predicate names are intentionally excluded from comparisons; observable atoms
and the complete set of minimal branches are compared instead.

`run.sh` is the stronger executable gate: it drives the matching Haskell and
Rust batch runners with the same scheduled inputs, then compares their complete
canonical histories and full-state semantic digests byte for byte. It covers
future and past operators, branching negative cycles, unsupported classical
blockers, pattern functions, term-level previous, arithmetic, and every shared
rejection case. Future-result coverage distinguishes the normative precedence
of conjunction over `until` and `atnext`. Arithmetic coverage includes
arbitrary-precision values,
canonical integer spellings, operator precedence, signed floor division, and
division-by-zero failure. Adversarial fresh-name cases also verify that source
predicates ending in `_auxN` remain observable while actual generated
predicates are hidden unless requested. Negative cases additionally cover
mixed predicate, constructor, and pattern-function arities; malformed
pattern-function relational calls; malformed built-in and arithmetic
signatures; and attempts to define an external built-in as a stored result.
The negative corpus also rejects unparenthesized chains of non-associative
past-time condition operators, non-ASCII identifiers, and `for` counts beyond
the portable executable expansion limit. Positive lexical
cases verify contextual keyword reservation and the separation of arithmetic
term operators from the predicate namespace. A positive lexical case executes
every documented Unicode alias, including both previous-time dot glyphs, and
distinguishes the black- and white-diamond source operators.
The executable gate also rejects scheduled inputs that change predicate or
constructor arity, reuse a pattern-function or generated predicate, inject a
built-in or term-level previous wrapper, or change a dynamically introduced
signature in a later world.

Run it from the repository root:

```sh
sh conformance/run.sh
```
