# Temporal Prolog

**Haskell and Rust implementations of Sakuragawa's (1986) temporal logic programming language**

## Overview

Temporal logic programming extends standard Prolog with the notion of **time**.
Where classical Prolog computes a single set of facts via backward chaining,
Temporal Prolog computes a *sequence* of **worlds** -- each world is the set of
ground atoms that hold true at a given time step. Rules can reference not only
the current world but also past worlds, and can assert facts that persist into
the future under specified conditions.

This is made possible by a family of **temporal operators** drawn from linear
temporal logic. Conditions (rule bodies) may use *past-time* operators like
`@` (previous), `#` (has-been), and `?` (once) to inspect the history of
worlds. Results (rule heads) may use *future-time* operators like `always`,
`until`, `atnext`, and `next` to project facts forward in time. Together these
let you express stateful, reactive, and process-control logic declaratively.

The implementations follow the paper closely: a five-step normalization
pipeline eliminates temporal operators by introducing auxiliary predicates,
producing rules in a canonical *normal form*. Condition-1 programs use a
stratified least-fixed-point fast path; finite negative cycles use the paper's
SCC-ordered set of classical minimal models and may produce multiple worlds.
Pattern functions (like list append) are resolved by alpha-renamed backward
chaining.

The project includes a complete [normative specification](output/pdf/temporal-prolog-specification.pdf)
with explicit errata for inconsistencies in the 1986 paper
([LaTeX source](spec/temporal-prolog.tex)).
Both engines execute the programs in the [shared conformance corpus](conformance/README.md).
They also provide matching bounded protocol model checkers over a shared
[scenario format and example suite](examples/model-checking/README.md).

## Quick start

### Build

```
cabal build
cd rust && cargo build
```

### Run the REPL

```
cabal run temporal-prolog
```

Both implementations provide matching batch runners that preserve every
minimal branch and print complete, deterministic world histories:

```sh
cabal run temporal-prolog-run -- \
  conformance/cases/negative_cycle.tpl --steps 1

cargo run --manifest-path rust/Cargo.toml --bin temporal-prolog-rs -- \
  conformance/cases/negative_cycle.tpl --steps 1
```

Their output is byte-identical, including a digest of the complete raw state.
Schedule external inputs with repeated `--assert STEP:ATOM` options and use
`--include-internal` to display normalization auxiliaries. Invalid groundness,
step counts, out-of-horizon inputs, and runtime signature changes are rejected
rather than ignored. Runtime signatures are checked against the compiled
program, pending assertions, and all prior worlds.
Generated predicates are tracked by normalization provenance, not guessed from
their spelling, so source names such as `cache_aux0` remain fully visible.
Programs are signature-checked before normalization: each predicate and
constructor has one arity in its own namespace, each pattern function has one
input arity and an output-extended relational arity, and built-in predicates
and arithmetic operators have their specified signatures. Built-in predicates
are conditions evaluated by the engine; they cannot be rule results or
externally asserted facts. Pattern-function relations and generated predicates
are likewise internal and cannot be injected through assertion streams.

Run `sh conformance/run.sh` to execute the positive and negative shared corpus
through both binaries and fail on any output or acceptance mismatch.
See [TESTING.md](TESTING.md) for the behavior-by-behavior coverage map and the
distinction between repository-level and standalone-crate tests.

Run `sh benchmarks/run.sh 100` for the matched digest-checked comparison.

### Model-check a protocol

Explore every minimal-model branch of the nondeterministic arbiter and write
the complete state tree as Graphviz DOT:

```sh
cabal run temporal-prolog-check -- \
  examples/model-checking/arbiter.tpmc --dot /tmp/arbiter.dot

cargo run --manifest-path rust/Cargo.toml \
  --bin temporal-prolog-check-rs -- \
  examples/model-checking/arbiter.tpmc --dot /tmp/arbiter-rs.dot
```

Both commands report two bounded-safe leaves. Scenarios schedule fixed external
facts, enumerate named input-choice groups over a finite horizon, and declare
forbidden stored-fact patterns as invariants. Programs can derive
`violation(...)` witnesses using the full Temporal Prolog language. Unsafe runs
print a shortest counterexample and exit with status 2:

```sh
cabal run temporal-prolog-check -- \
  examples/model-checking/commit-buggy.tpmc
```

You will see a prompt like:

```
Temporal Prolog — based on Sakuragawa 1986
Type :help for available commands.
>
```

### Load an example

```
> :load examples/foot_warmer.tpl
Loaded 3 rules and 0 pattern functions from examples/foot_warmer.tpl
```

### Step through worlds

Assert some facts and advance time:

```
> :assert hot(heater)
> :step
0> :world
World 0:
  device(heater)
  hot(heater)
  off(heater)
```

Step again without asserting anything:

```
0> :step
1> :world
World 1:
  device(heater)
  on(heater)
```

In world 1 no `hot(heater)` is asserted, so `~hot(heater)` succeeds and the
controller turns the heater on. The `device(heater)` fact binds `X` before the
negation check, ensuring ground results (see [Notes on negation](#notes-on-negation)).

Use `:history` to see all worlds at once.

## Syntax reference

### Temporal operators

| ASCII | Unicode | Position  | Meaning                                     |
|-------|---------|-----------|---------------------------------------------|
| `@`   | `●` / `•` | Condition | **Previous** -- true at the previous time   |
| `~`   | `¬`     | Condition | **Negation** -- negation-as-failure         |
| `#`   | `■`     | Condition | **Has-been** -- true at every step from 0   |
| `?`   | `◆`     | Condition | **Once** -- true at some past step          |
| `eventually` | `◇` | Condition | Synonym for once (past-time)           |
| `since` | --    | Condition | `a since b` -- a held since b became true   |
| `after` | --    | Condition | `a after b` -- `b` occurred strictly before `a`; the witness remains true |
| `for`   | --    | Condition | `a for n` -- a held for `n > 0` consecutive steps |
| `always` | `□`  | Result    | **Always** -- holds from now on             |
| `until`  | --   | Result    | `r until c` -- r holds until c becomes true |
| `atnext` | --   | Result    | `r atnext c` -- r fires when c next holds   |
| `next`   | `○`  | Result    | **Next** -- holds at the next time step     |

Both U+25CF BLACK CIRCLE (`●`) and U+2022 BULLET (`•`) spell previous
time. U+25C6 BLACK DIAMOND (`◆`) spells `once`, while U+25C7 WHITE DIAMOND
(`◇`) spells `eventually`. The last two normalize to the same past-existential
semantics but remain distinct constructors in the source AST.

### Names and namespaces

Identifiers are ASCII-only. Variables begin with an uppercase letter; names
begin with a lowercase letter or underscore. Unicode is accepted only for the
operator aliases above.

Temporal control words are reserved as predicate and pattern-function names,
but remain valid constructor names where a term is expected, such as
`tag(always)` or `payload(true)`. Predicate and constructor namespaces remain
independent: `div/2` and `mod/2` may be ordinary predicates even though their
term forms are arithmetic operators. The prefix external forms `true()`,
`false()`, and `is(L, R)` are accepted and canonicalized by the pretty-printer.

### Operator precedence (tightest to loosest)

For conditions:

1. Unary: `@`, `~`, `#`, `?`, `eventually`
2. Conjunction: `/\`
3. Binary temporal operators: `since`, `after`, `for`
4. Implication: `=>`

For results:

1. Unary: `always`, `next`
2. Conjunction: `/\`
3. Binary temporal operators: `until`, `atnext`
4. Implication: `=>`

`until` and `atnext` are non-associative, so nested uses require parentheses.
In particular, `p /\ q until stop` means `(p /\ q) until stop`.
The binary condition operators `since`, `after`, and `for` are likewise
non-associative; write `(a since b) after c` when nesting them.

## Rule syntax

**Implication rules** have the form:

```
condition => result.
```

Every rule ends with a period. The condition (body) is a conjunction of
temporal formulas; the result (head) is an atom or temporal result formula.

**Facts** are rules with no condition:

```
result.
```

**Pattern functions** define term-level rewriting with support for recursion:

```
append([], X) -> X.
append([H|T], Y) -> [H|append(T, Y)].
```

Pattern functions are resolved via backward chaining (SLD-resolution) at
query time, so recursive definitions like `append` work naturally. They can
be used inside rule conditions and heads:

```
a(X) /\ b(Y) => combined(append(X, Y)).
```

The conditional reduction form from Section 5.1 of the paper is also
supported:

```prolog
enabled(X) => choose(X) -> selected.
```

The term-level `@` operator applies to a pattern-function value. During
normalization, `present(@lookup(key))` becomes a current-world
`present(Value)` condition together with a previous-world
`@lookup(key, Value)` condition; it does not move `present` into the previous
world.

**Conjunction** uses `/\`:

```
hot(X) /\ @running(X) => alarm(X).
```

**Comments** start with `%` and extend to end of line:

```
% This is a comment
hot(X) => off(X).  % inline comment
```

**Variables** start with an uppercase letter (`X`, `Room`). **Atoms** and
**predicates** start with a lowercase letter or underscore (`hot`, `_aux`).
**Numbers** are arbitrary-precision integers (`-3`, `0`, `42`). Leading zeros
do not create distinct terms: `007` is the integer `7`, and `-0` is `0`.
Arithmetic terms support infix `+`, `-`, `*`, `div`, and `mod`; `div` and
`mod` have the same precedence as multiplication and associate to the left.
Division rounds toward negative infinity, with the remainder taking the sign
of the divisor. Division by zero and nonground or noninteger arithmetic fail
without binding. The repetition count in `for` is parsed as an exact positive
integer rather than a machine word. The portable executable profile admits at
most 1,000 repetitions; larger counts are rejected as normalization resource
errors before expansion, never truncated or wrapped.

Both libraries can parse and pretty-print source ASTs without changing their
structure. The Rust API exposes `parse_term`, `parse_condition`, `parse_result`,
and `parse_rule` alongside `pretty_term`, `pretty_condition`, `pretty_result`,
`pretty_rule`, and `pretty_program`; round-trip tests cover every grammar form
and precedence boundary.

## REPL commands

| Command            | Description                                       |
|--------------------|---------------------------------------------------|
| `:load <file>`     | Load a Temporal Prolog program from file          |
| `:step [n]`        | Advance n worlds (default 1)                      |
| `:assert <atom>`   | Assert a ground fact for the next step            |
| `:query <atom>`    | Query facts, pattern functions, or built-ins      |
| `:world`           | Show facts in the current world                   |
| `:history`         | Show all computed worlds                          |
| `:program`         | Show source and normalized program                |
| `:trace`           | Show which rules derived each fact                |
| `:save <file>`     | Save the current program to a file                |
| `:reset`           | Reset the interpreter state                       |
| `:help`            | Show help                                         |
| `:quit`            | Exit the REPL                                     |

Queries use the same external evaluator as rule conditions, so equality,
arithmetic, comparisons, `at(N)`, `true`, and `false` return answers and
bindings directly. For example, `:query X is 2 + 3` returns `X = 5`.
Malformed signatures are reported as errors instead of being treated as
logical failure.

You can also type a rule directly at the prompt to add it to the program:

```
> hot(X) => off(X).
Added: hot(X) => off(X).
```

## Examples

### Foot warmer controller

The foot warmer example (from Sakuragawa 1986, Section 4.2) models a simple
on/off controller:

```prolog
% foot_warmer.tpl
device(heater).
device(X) /\ hot(X) => off(X).
device(X) /\ ~hot(X) => on(X).
```

REPL session:

```
> :load examples/foot_warmer.tpl
Loaded 3 rules and 0 pattern functions from examples/foot_warmer.tpl
> :assert hot(heater)
> :step
0> :world
World 0:
  device(heater)
  hot(heater)
  off(heater)
0> :step
1> :world
World 1:
  device(heater)
  on(heater)
```

When `hot(heater)` is asserted, the controller derives `off(heater)`. In
world 1 no `hot` fact is asserted, so `~hot(heater)` succeeds and the
controller derives `on(heater)`. The `device(heater)` domain fact binds `X`
before the negation check, ensuring ground results.

### List append

The append example demonstrates recursive pattern functions:

```prolog
% append.tpl
append([], X) -> X.
append([A|X], Y) -> [A|append(X, Y)].

list([1, 2, 3]).
list([4, 5]).

list(X) /\ list(Y) /\ append(X, Y, Z) => combined(Z).
```

REPL session:

```
> :load examples/append.tpl
Loaded 3 rules and 2 pattern functions from examples/append.tpl
> :step
0> :query combined(X)
Yes.
  X = [1, 2, 3, 1, 2, 3]
  X = [1, 2, 3, 4, 5]
  X = [4, 5, 1, 2, 3]
  X = [4, 5, 4, 5]
```

Pattern function definitions are normalized into predicate clauses (e.g.
`append([], X) -> X.` becomes the clause `append([], X, X).`). When a rule
condition references a pattern-function predicate, the interpreter resolves it
via backward chaining (SLD-resolution) rather than world lookup, so recursive
definitions work naturally.

### Mutual exclusion

The mutual exclusion example (Section 4.6) demonstrates the `@` operator for
referencing the previous world:

```prolog
% mutual_exclusion.tpl
assign(X) /\ @assigned_to(X) => assigned_to(X).
assign(1) /\ ~@assigned_to_something => assigned_to(1).
assign(2) /\ ~assign(1) /\ ~@assigned_to_something => assigned_to(2).
assigned_to(X) => assigned_to_something.
```

REPL session:

```
> :load examples/mutual_exclusion.tpl
Loaded 4 rules and 0 pattern functions from examples/mutual_exclusion.tpl
> :assert assign(1)
> :assert assign(2)
> :step
0> :world
World 0:
  assign(1)
  assign(2)
  assigned_to(1)
  assigned_to_something
```

Process 1 gets priority because its rule is checked first and process 2's rule
requires `~assign(1)`. The `@assigned_to(X)` condition means that once
assigned, a process retains the resource as long as it keeps requesting it.

## Architecture

The implementation follows a five-phase pipeline:

1. **Parse** (`TemporalProlog.Parser`): Megaparsec-based parser converts
   source text into an AST of rules, conditions, results, and pattern
   functions. Supports both ASCII and Unicode operator syntax.

2. **Normalize** (`TemporalProlog.Normalizer`): A five-step transformation
   pipeline (paper Section 5.1, pp. 10-14) first validates source symbol
   signatures, then eliminates temporal operators by introducing auxiliary
   predicates:
   - Step 1: Eliminate `always`, `until`, `atnext`, `next`; split conjunctions
   - Step 2: Eliminate `since`, `after`, `for`, `has-been`, `once`
   - Step 3: Expand pattern functions into predicate clauses, transferring
     term-level `@` depth to the generated pattern-function conditions
   - Step 4: Push negation to atomic level
   - Step 5: Distribute `@` over `/\` into canonical form `@^m(~?)atom`

   The normalizer is pure (`State` + `ExceptT` for fresh names and error
   reporting) and returns either a structured error or the normalized program
   with any safety warnings.

3. **Interpret** (`TemporalProlog.Interpreter`): A hybrid execution engine:
   - **Forward chaining** computes condition-1 programs by stratified least
     fixed points. Finite current-world negative SCCs are handled by candidate
     enumeration and the paper's SCC-lexicographic classical minimal-model
     order. `stepWorldAll` exposes every branch; `stepWorld` chooses a stable
     canonical branch.
   - **Backward chaining** (SLD-resolution) resolves pattern-function
     predicates on demand, with alpha-renaming and an explicit resource error
     at the recursion limit. Pattern-function rules are excluded from
     stratification since they don't participate in the forward-chaining
     fixed point.

   External predicates (`=`, `is`, `>`, `<`, `>=`, `<=`, `at`, `true`,
   `false`) are evaluated specially in both rule conditions and public
   queries. Runtime atoms are signature-checked before assertion or query;
   generated predicates and pattern-function relations cannot be asserted.

4. **Model-check** (`TemporalProlog.ModelChecker`): A breadth-first bounded
   explorer applies every Cartesian product of configured input choices to
   every active branch, calls `stepWorldAll`, checks forbidden stored-fact
   patterns in every new world, and retains parent links for shortest
   counterexamples and DOT output. Violating branches stop immediately;
   nonviolating branches continue to the horizon. A successful result is
   reported as `BOUNDED_SAFE`, never as an unqualified global safety proof.
   The Rust `model_checker` module implements the same algorithm and produces
   byte-identical summaries and graphs for the shared examples.

5. **Differentially validate** (`TemporalProlog.Batch`, `rust::batch`): The
   matching batch runners preserve all minimal branches, canonically sort
   complete histories, and hash the full raw state. The shared conformance gate
   compares byte-for-byte output across temporal operators, pattern functions,
   arithmetic, recursion through negation, fresh-name collisions, malformed
   source and runtime signatures, built-in misuse, internal-name injection,
   and the other specified rejection cases.

At world 0, every previous-time formula `@F` is false, exactly as defined in
Section 5.2. In particular, `@~p` is false there, while `~@p` is true; the
normalizer introduces the auxiliary predicate required by Step 4 to preserve
that distinction.

The executable profile requires finite candidate generation and range-restricted
forward rules. Resource limits and unsafe rules are reported as errors rather
than being treated as logical failure. The independent Rust crate in `rust/`
implements the same parser, normalization, backward chainer, stratified fast
path, and general minimal-model evaluator.

As an independent check on the shared transition semantics, both test suites
compare the general evaluator against a direct exhaustive truth-table oracle
over all 1,024 programs generated from a ten-rule, two-atom basis.

One additional paper bug is observable: the Section 4.7 assignment clauses
have three classical minimal models, not the claimed two. The third contains
only unsupported `assigned_to_another` blockers. Both engines expose all three
for the published program; the specification gives a corrected two-choice
encoding.

Supporting modules:
- `TemporalProlog.Syntax`: Core AST types (user-facing and normalized)
- `TemporalProlog.Unification`: First-order term unification with occurs check
- `TemporalProlog.PrettyPrint`: Human-readable display for all AST types
- `TemporalProlog.Batch`: Deterministic branch-preserving batch execution
- `TemporalProlog.Scenario`: Portable schedules and invariant declarations
- `TemporalProlog.ModelChecker`: Branch exploration, traces, and DOT rendering

## Notes on negation

Negation in Temporal Prolog is **negation-as-failure** under the closed-world
assumption, following standard Prolog semantics. `~p(X)` checks whether any
matching `p(...)` exists -- it does not enumerate values of X for which `p(X)` is
false. Variables in negated conditions must be bound by a preceding positive
condition:

```prolog
r(X) /\ ~p(X) => q(X).    % correct: X is bound by r(X) first
~p(X) => q(X).             % X is unbound -- execution rejects this rule
```

The foot warmer example demonstrates this pattern: `device(X) /\ ~hot(X) => on(X)`
uses the domain fact `device(heater)` to bind `X` before the negation check.

## References

Sakuragawa, T. (1986). "Temporal Prolog." *RIMS Kokyuroku* 586, 305-329.
