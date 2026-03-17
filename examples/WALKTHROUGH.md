# Temporal Prolog REPL Walkthrough

This document shows a complete interactive session with the Temporal Prolog
REPL. The prompt is `"> "` before any step; after stepping to world N the
prompt becomes `"N> "`.

---

## 1. Starting up and loading the foot warmer example

```
$ temporal-prolog
Temporal Prolog — based on Sakuragawa 1986
Type :help for available commands.
> :help
Commands:
  :load <file>    Load a Temporal Prolog program
  :step [n]       Advance n worlds (default 1)
  :assert <atom>  Assert a ground fact for the next step
  :query <atom>   Query the current world
  :world          Show the current world
  :history        Show all past worlds
  :program        Show the loaded program
  :trace          Show which rules derived each fact
  :save <file>    Save the current program to a file
  :examples       Show example programs
  :reset          Reset the interpreter
  :help           Show this help
  :quit           Exit

  Or type a rule directly to add it to the program.
  Example: temperature(X) > 100 => alarm(X).
```

Load the foot warmer controller:

```
> :load examples/foot_warmer.tpl
Loaded 2 rules and 0 pattern functions from examples/foot_warmer.tpl
> :program
=== Source Program ===
hot(X) => off(X).
~hot(X) => on(X).
=== Normalized Program ===
hot(X) => off(X).
~hot(X) => on(X).
```

## 2. Asserting facts and stepping

Assert that device `heater` is hot, then advance one time step:

```
> :assert hot(heater)
> :step
0> :world
World 0:
  hot(heater)
  off(heater)
```

The rule `hot(X) => off(X)` fired. Now suppose the heater cools down — we
assert nothing about it being hot and step again:

```
0> :step
1> :world
World 1:
```

Under the Closed World Assumption, `hot(heater)` is no longer true at world 1.
The rule `~hot(X) => on(X)` has negation succeed (no `hot` facts), but `X`
remains unbound so `on(X)` is non-ground and is filtered out. World 1 is empty.

## 3. Querying

```
1> :query off(X)
No.
1> :query hot(X)
No.
```

## 4. Viewing history

```
1> :history
World 0:
  hot(heater)
  off(heater)
World 1:
```

---

## 5. Traffic light state machine

```
> :reset
State reset.
> :load examples/traffic_light.tpl
Loaded 6 rules and 0 pattern functions from examples/traffic_light.tpl
```

Start the light in `green` and let the timer run without expiring:

```
> :assert green
> :step
0> :world
World 0:
  green
```

The persistence rule `green /\ ~timer_expired => next green` keeps the light
green across worlds. Step again without asserting `timer_expired`:

```
0> :step
1> :world
World 1:
  green
```

Now trigger the timer:

```
1> :assert timer_expired
1> :step
2> :world
World 2:
  green
  timer_expired
```

At world 2, the previous world's `green` carries forward (via the `next`
persistence auxiliary), and `timer_expired` is asserted. The transition rule
`green /\ timer_expired => next yellow` fires, scheduling `yellow` for the
next world. On the next step, the timer is no longer asserted:

```
2> :step
3> :world
World 3:
  yellow
```

Trigger the timer again to move to red:

```
3> :assert timer_expired
3> :step
4> :world
World 4:
  timer_expired
  yellow
```

```
4> :step
5> :world
World 5:
  red
```

And once more back to green:

```
5> :assert timer_expired
5> :step
6> :world
World 6:
  red
  timer_expired
```

```
6> :step
7> :world
World 7:
  green
```

---

## 6. Append — pattern functions

```
> :reset
State reset.
> :load examples/append.tpl
Loaded 3 rules and 2 pattern functions from examples/append.tpl
> :program
=== Source Program ===
list([1, 2, 3]).
list([4, 5]).
list(X) /\ list(Y) /\ append(X, Y, Z) => combined(Z).

append([], X) -> X.
append([A|X], Y) -> [A|append(X, Y)].
=== Normalized Program ===
...
```

Step to compute the first world:

```
> :step
0> :world
World 0:
  list([1, 2, 3])
  list([4, 5])
```

The two `list` facts are derived. The `combined` rule depends on the
`append` pattern function; recursive pattern function expansion is not yet
fully supported, so `combined(Z)` is not derived in the current
implementation:

```
0> :query list(X)
Yes.
  X = [1, 2, 3]
  X = [4, 5]
0> :query combined(X)
No.
```

---

## 7. Adding rules interactively

You can type rules directly at the prompt without loading a file:

```
> :reset
State reset.
> temperature(X) /\ X > 100 => alarm.
Added: temperature(X) /\ X > 100 => alarm.
> :assert temperature(150)
> :step
0> :query alarm
Yes.
  {}
```

The empty substitution `{}` means the query matched with no variable bindings,
which is expected for the ground atom `alarm`.

Note: the comparison `X > 100` must be a separate conjunct. Writing
`temperature(X) > 100` would be parsed as a single infix atom (a comparison
between the term `temperature(X)` and `100`), which is not what we want.

---

## Tips

- **Assertions are consumed**: `:assert` queues a fact for the *next* `:step`.
  After that step the fact is present only if a rule continues to derive it.
- **Closed World Assumption**: anything not derived or asserted is false.
- **Previous-time operator (`@`)**: references the world from the prior step.
  At world 0 there is no prior world, so `@p` is always false.
- **`next` in rule heads**: the derived atom appears in the *next* world, not
  the current one.
- **Non-ground negation**: when a negated condition like `~hot(X)` succeeds
  with unbound variables, the head remains non-ground and is filtered out.
  Negated conditions should be "safe" — all variables should be bound by
  positive conditions first.
