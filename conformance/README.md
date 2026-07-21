# Shared conformance corpus

Every `.tpl` file in `cases/` is parsed and executed by both implementations;
every file in `rejections/` must fail parsing, normalization, or executable-
profile validation at the documented boundary.
The Haskell suite in `test/Main.hs` and the Rust integration suite in
`rust/tests/conformance.rs` assert the same semantic outcomes. Internal fresh
predicate names are intentionally excluded from comparisons; observable atoms
and the complete set of minimal branches are compared instead.
