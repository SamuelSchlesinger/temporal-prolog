# Protocol model-checking examples

The bounded model checker explores every classical minimal-model branch of a
Temporal Prolog program. Both implementations consume the same `.tpmc`
scenario files and produce the same tree statistics and counterexample traces.
The checked-in `.expected` and `.expected.dot` files are shared golden outputs
used by both test suites.

Run the safe nondeterministic arbiter with either engine:

```sh
cabal run temporal-prolog-check -- \
  examples/model-checking/arbiter.tpmc --dot /tmp/arbiter.dot

cargo run --quiet --manifest-path rust/Cargo.toml \
  --bin temporal-prolog-check-rs -- \
  examples/model-checking/arbiter.tpmc --dot /tmp/arbiter-rs.dot
```

The arbiter has two bounded-safe leaves, one per grant choice. The correct
commit scenario independently chooses yes or no for each participant, checking
all four valid vote combinations in one run:

```sh
cabal run temporal-prolog-check -- examples/model-checking/commit-safe.tpmc
```

The deliberately broken coordinator exits with status 2 and prints a shortest
counterexample showing simultaneous `decision(tx1,commit)` and
`decision(tx1,abort)`:

```sh
cabal run temporal-prolog-check -- examples/model-checking/commit-buggy.tpmc
```

Render a generated tree with Graphviz, for example:

```sh
dot -Tsvg /tmp/arbiter.dot -o /tmp/arbiter.svg
```

## Scenario format

Scenarios are line-oriented. Blank lines and `%` comments are ignored.

```text
name two-client-arbiter
program arbiter.tpl
steps 4
assert 0 request(1)
choose 1 p1_vote vote_yes(tx1, p1)
choose 1 p1_vote vote_no(tx1, p1)
invariant mutual_exclusion forbids violation(mutual_exclusion)
```

- `name NAME` supplies the stable report and graph name.
- `program PATH` is resolved relative to the scenario file.
- `steps N` sets a positive, finite number of worlds to explore.
- `assert STEP ATOM` supplies a ground external fact at a zero-indexed world.
- `choose STEP GROUP ATOM` adds a ground alternative to a named input group.
  Exactly one alternative per group is selected, and independent groups form a
  Cartesian product. Use the reserved alternative `none` to include absence of
  an input.
- `invariant NAME forbids ATOM` fails when the atom pattern matches a stored
  fact in the current world. Variables are allowed, so
  `violation(problem, X)` catches every stored ground instance. Pattern-function
  query results are deliberately not world facts and therefore do not match.

Programs normally derive explicit `violation(...)` witnesses. This keeps
invariants expressive without introducing a second logic language: ordinary
Temporal Prolog conjunction, arithmetic, and temporal rules decide when the
witness exists, while the scenario only names the forbidden pattern.

Exploration is breadth-first and deterministic. A violating branch stops at
its first bad world; other branches continue to the horizon. DOT nodes contain
observable facts by default. Pass `--include-internal` to show normalization
auxiliaries as well.

`BOUNDED_SAFE` has a deliberately narrow meaning: no forbidden fact occurred
on any internal minimal-model branch, for any configured input-choice
combination, during the declared number of worlds. It does not quantify over
inputs omitted from the scenario, later worlds, or liveness properties.
`UNSAFE`, by contrast, includes a concrete finite counterexample.

Both engine suites also run an independent exhaustive propositional oracle:
all 1,024 programs from a ten-rule two-atom basis are evaluated by a direct
truth-table model enumerator and compared with the general transition engine.
