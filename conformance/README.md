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
rejection case. Arithmetic coverage includes arbitrary-precision values,
canonical integer spellings, operator precedence, signed floor division, and
division-by-zero failure. Adversarial fresh-name cases also verify that source
predicates ending in `_auxN` remain observable while actual generated
predicates are hidden unless requested.

Run it from the repository root:

```sh
sh conformance/run.sh
```
