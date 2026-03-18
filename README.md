# Temporal Prolog

**A Haskell implementation of Sakuragawa's (1986) temporal logic programming language**

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

The implementation follows the paper closely: a five-step normalization
pipeline eliminates temporal operators by introducing auxiliary predicates,
producing rules in a canonical *normal form*. A stratified, least-fixed-point
interpreter then computes each world in sequence, using negation-as-failure
under the closed-world assumption. Pattern functions (like list append) are
resolved via backward chaining, supporting full recursion.

## Quick start

### Build

```
cabal build
```

### Run the REPL

```
cabal run temporal-prolog
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
| `@`   | `●`     | Condition | **Previous** -- true at the previous time   |
| `~`   | `¬`     | Condition | **Negation** -- negation-as-failure         |
| `#`   | `■`     | Condition | **Has-been** -- true at every step from 0   |
| `?`   | `◆`     | Condition | **Once** -- true at some past step          |
| `eventually` | `◇` | Condition | Synonym for once (past-time)           |
| `since` | --    | Condition | `a since b` -- a held since b became true   |
| `after` | --    | Condition | `a after b` -- a held, then b became true   |
| `for`   | --    | Condition | `a for n` -- a held for n consecutive steps |
| `always` | `□`  | Result    | **Always** -- holds from now on             |
| `until`  | --   | Result    | `r until c` -- r holds until c becomes true |
| `atnext` | --   | Result    | `r atnext c` -- r fires when c next holds   |
| `next`   | `○`  | Result    | **Next** -- holds at the next time step     |

### Operator precedence (tightest to loosest)

1. Unary: `@`, `~`, `#`, `?`
2. Binary: `since`, `after`, `for`, `until`, `atnext`
3. Conjunction: `/\`
4. Implication: `=>`

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
**Numbers** are non-negative integers (`0`, `42`).

## REPL commands

| Command            | Description                                       |
|--------------------|---------------------------------------------------|
| `:load <file>`     | Load a Temporal Prolog program from file          |
| `:step [n]`        | Advance n worlds (default 1)                      |
| `:assert <atom>`   | Assert a ground fact for the next step            |
| `:query <atom>`    | Query the current world (or pattern functions)    |
| `:world`           | Show facts in the current world                   |
| `:history`         | Show all computed worlds                          |
| `:program`         | Show source and normalized program                |
| `:trace`           | Show which rules derived each fact                |
| `:save <file>`     | Save the current program to a file                |
| `:reset`           | Reset the interpreter state                       |
| `:help`            | Show help                                         |
| `:quit`            | Exit the REPL                                     |

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

The implementation follows a three-phase pipeline:

1. **Parse** (`TemporalProlog.Parser`): Megaparsec-based parser converts
   source text into an AST of rules, conditions, results, and pattern
   functions. Supports both ASCII and Unicode operator syntax.

2. **Normalize** (`TemporalProlog.Normalizer`): A five-step transformation
   pipeline (paper Section 5.1, pp. 10-14) eliminates temporal operators by
   introducing auxiliary predicates:
   - Step 1: Eliminate `always`, `until`, `atnext`, `next`; split conjunctions
   - Step 2: Eliminate `since`, `after`, `for`, `has-been`, `once`
   - Step 2.5: Lift term-level `@` (TPrev) to condition-level `@` (CPrev)
   - Step 3: Expand pattern functions into predicate clauses
   - Step 4: Push negation to atomic level
   - Step 5: Distribute `@` over `/\` into canonical form `@^m(~?)atom`

   The normalizer is pure (`State` + `ExceptT` for fresh names and error
   reporting) and returns either a structured error or the normalized program
   with any safety warnings.

3. **Interpret** (`TemporalProlog.Interpreter`): A hybrid execution engine:
   - **Forward chaining** computes each world as a stratified least fixed
     point of the normalized rules, using negation-as-failure under the
     closed-world assumption.
   - **Backward chaining** (SLD-resolution) resolves pattern-function
     predicates on demand, with alpha-renaming and a depth limit for
     termination safety. Pattern-function rules are excluded from
     stratification since they don't participate in the forward-chaining
     fixed point.

   External predicates (`=`, `>`, `<`, `>=`, `<=`, `at`, `true`, `false`)
   are evaluated specially.

Supporting modules:
- `TemporalProlog.Syntax`: Core AST types (user-facing and normalized)
- `TemporalProlog.Unification`: First-order term unification with occurs check
- `TemporalProlog.PrettyPrint`: Human-readable display for all AST types

## Notes on negation

Negation in Temporal Prolog is **negation-as-failure** under the closed-world
assumption, following standard Prolog semantics. `~p(X)` checks whether any
matching `p(...)` exists -- it does not enumerate values of X for which `p(X)` is
false. Variables in negated conditions must be bound by a preceding positive
condition:

```prolog
r(X) /\ ~p(X) => q(X).    % correct: X is bound by r(X) first
~p(X) => q(X).             % X is unbound -- the safety validator warns
```

The foot warmer example demonstrates this pattern: `device(X) /\ ~hot(X) => on(X)`
uses the domain fact `device(heater)` to bind `X` before the negation check.

## References

Sakuragawa, H. (1986). "Temporal Prolog." *RIMS Kokyuroku*, 221-238.
