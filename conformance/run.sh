#!/bin/sh
set -eu

work_dir=$(mktemp -d "${TMPDIR:-/tmp}/temporal-prolog-conformance.XXXXXX")
trap 'rm -rf "$work_dir"' EXIT HUP INT TERM

cabal build temporal-prolog-run >/dev/null
cargo build --quiet --manifest-path rust/Cargo.toml --bin temporal-prolog-rs

haskell_runner=$(cabal list-bin temporal-prolog-run)
rust_runner=rust/target/debug/temporal-prolog-rs

check_case() {
  case_name=$1
  program=$2
  shift 2
  "$haskell_runner" "$program" "$@" >"$work_dir/haskell.out"
  "$rust_runner" "$program" "$@" >"$work_dir/rust.out"
  if ! diff -u "$work_dir/haskell.out" "$work_dir/rust.out"; then
    printf 'cross-engine mismatch: %s\n' "$case_name" >&2
    exit 1
  fi
  printf 'PASS %s\n' "$case_name"
}

reject_case() {
  case_name=$1
  program=$2
  shift 2
  if "$haskell_runner" "$program" "$@" >/dev/null 2>&1; then
    printf 'Haskell unexpectedly accepted %s\n' "$case_name" >&2
    exit 1
  fi
  if "$rust_runner" "$program" "$@" >/dev/null 2>&1; then
    printf 'Rust unexpectedly accepted %s\n' "$case_name" >&2
    exit 1
  fi
  printf 'PASS %s rejected\n' "$case_name"
}

check_case initial-world conformance/cases/initial_world.tpl
check_case strict-after conformance/cases/after_strict.tpl --steps 3 \
  --assert 0:restart --assert 1:monitoring
check_case append conformance/cases/append.tpl
check_case negative-cycle conformance/cases/negative_cycle.tpl
check_case paper-4.7 conformance/cases/paper_4_7.tpl \
  --assert '0:assign(1)' --assert '0:assign(2)'
check_case unsupported-blocker conformance/cases/unsupported_blocker.tpl
check_case future-results conformance/cases/future_results.tpl --steps 4 \
  --assert 0:trigger --assert 2:release --assert 2:stop
check_case future-results-internal conformance/cases/future_results.tpl --steps 4 \
  --assert 0:trigger --assert 2:release --assert 2:stop --include-internal
check_case result-precedence conformance/cases/result_precedence.tpl --steps 2 \
  --assert 0:start --assert 0:arm --assert 1:fire
check_case unicode-aliases conformance/cases/unicode_aliases.tpl --steps 2
check_case keyword-constructors conformance/cases/keyword_constructors.tpl --steps 1
check_case arithmetic-predicates conformance/cases/arithmetic_predicates.tpl --steps 1 \
  --assert '0:div(a,b)' --assert '0:mod(c,d)'
check_case past-conditions conformance/cases/past_conditions.tpl --steps 3 \
  --assert 0:ready --assert 0:start --assert 0:event --assert 1:ready
check_case term-previous conformance/cases/term_previous.tpl --steps 2 \
  --assert '0:present(value)' --assert '1:present(value)'
check_case arithmetic conformance/cases/arithmetic.tpl \
  --assert '0:value(4)' --assert '0:value(5)' \
  --assert '0:pair(a,a)' --assert '0:pair(a,b)'
check_case arithmetic-edges conformance/cases/arithmetic_edges.tpl
check_case conditional-reduction conformance/cases/conditional_reduction.tpl \
  --assert '0:enabled(a)' --assert '0:request(a)'
check_case auxiliary-collision conformance/cases/auxiliary_collision.tpl --steps 2 \
  --assert 0:trigger
check_case auxiliary-collision-internal conformance/cases/auxiliary_collision.tpl --steps 2 \
  --assert 0:trigger --include-internal

reject_case for-zero conformance/rejections/for_zero.tpl
reject_case missing-period conformance/rejections/missing_period.tpl
reject_case plain-previous-term conformance/rejections/plain_previous_term.tpl
reject_case unsafe-range conformance/rejections/unsafe_range.tpl
reject_case mixed-predicate-arity conformance/rejections/mixed_predicate_arity.tpl
reject_case mixed-constructor-arity conformance/rejections/mixed_constructor_arity.tpl
reject_case mixed-pattern-arity conformance/rejections/mixed_pattern_arity.tpl
reject_case malformed-pattern-relation conformance/rejections/malformed_pattern_relation.tpl
reject_case builtin-result conformance/rejections/builtin_result.tpl
reject_case malformed-builtin conformance/rejections/malformed_builtin.tpl
reject_case malformed-arithmetic conformance/rejections/malformed_arithmetic.tpl
reject_case chained-temporal-condition conformance/rejections/chained_temporal_condition.tpl
reject_case non-ascii-identifier conformance/rejections/non_ascii_identifier.tpl
reject_case for-count-overflow conformance/rejections/for_count_overflow.tpl
reject_case asserted-predicate-arity conformance/cases/initial_world.tpl \
  --assert '0:p(x)'
reject_case asserted-constructor-arity conformance/cases/term_previous.tpl \
  --assert '0:present(key(a))'
reject_case asserted-pattern-relation conformance/cases/append.tpl \
  --assert '0:append([],[],[])'
reject_case asserted-generated-predicate conformance/cases/future_results.tpl \
  --assert 0:next_aux1
reject_case historical-input-arity conformance/cases/initial_world.tpl \
  --steps 2 --assert 0:event --assert '1:event(a)'
reject_case asserted-builtin conformance/cases/initial_world.tpl \
  --assert '0:at(0)'
reject_case asserted-term-previous conformance/cases/initial_world.tpl \
  --assert '0:event(@value)'
reject_case asserted-malformed-arithmetic conformance/cases/initial_world.tpl \
  --assert '0:event(div(1))'

printf 'All cross-engine conformance cases agree.\n'
