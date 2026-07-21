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
  if "$haskell_runner" "$program" >/dev/null 2>&1; then
    printf 'Haskell unexpectedly accepted %s\n' "$case_name" >&2
    exit 1
  fi
  if "$rust_runner" "$program" >/dev/null 2>&1; then
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
check_case past-conditions conformance/cases/past_conditions.tpl --steps 3 \
  --assert 0:ready --assert 0:start --assert 0:event --assert 1:ready
check_case term-previous conformance/cases/term_previous.tpl --steps 2 \
  --assert '0:present(value)' --assert '1:present(value)'
check_case arithmetic conformance/cases/arithmetic.tpl \
  --assert '0:value(4)' --assert '0:value(5)' \
  --assert '0:pair(a,a)' --assert '0:pair(a,b)'
check_case conditional-reduction conformance/cases/conditional_reduction.tpl \
  --assert '0:enabled(a)' --assert '0:request(a)'

reject_case for-zero conformance/rejections/for_zero.tpl
reject_case missing-period conformance/rejections/missing_period.tpl
reject_case plain-previous-term conformance/rejections/plain_previous_term.tpl
reject_case unsafe-range conformance/rejections/unsafe_range.tpl

printf 'All cross-engine conformance cases agree.\n'
