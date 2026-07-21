#!/bin/sh
set -eu

iterations=${1:-100}

cabal build temporal-prolog-bench >/dev/null
cargo build --release --manifest-path rust/Cargo.toml --bin temporal-prolog-bench >/dev/null

for length in 25 100; do
  haskell_output=$(cabal run temporal-prolog-bench -- "$length" 20 "$iterations" 2>/dev/null)
  rust_output=$(rust/target/release/temporal-prolog-bench "$length" 20 "$iterations")
  printf '%s\n' "$haskell_output"
  printf '%s\n' "$rust_output"
  haskell_digest=${haskell_output##*digest=}
  rust_digest=${rust_output##*digest=}
  if [ "$haskell_digest" != "$rust_digest" ]; then
    printf 'semantic digest mismatch for length %s\n' "$length" >&2
    exit 1
  fi
done
