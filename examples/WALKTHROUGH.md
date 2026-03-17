# Temporal Prolog REPL Walkthrough

This document shows a complete interactive session with the Temporal Prolog
REPL. Lines starting with a world number and `>` are prompts; everything else
is output from the system.

---

## 1. Starting up and loading the foot warmer example

```
$ temporal-prolog
Temporal Prolog — based on Sakuragawa 1986
Type :help for available commands.
0> :help
Commands:
  :load <file>    Load a Temporal Prolog program
  :step [n]       Advance n worlds (default 1)
  :assert <atom>  Assert a ground fact for the next step
  :query <atom>   Query the current world
  :world          Show the current world
  :history        Show all past worlds
  :program        Show the loaded program
  :reset          Reset the interpreter
  :help           Show this help
  :quit           Exit

  Or type a rule directly to add it to the program.
  Example: temperature(X) > 100 => alarm(X).
```

Load the foot warmer controller:

```
0> :load examples/foot_warmer.tpl
Loaded 2 rules and 0 pattern functions from examples/foot_warmer.tpl
0> :program
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
0> :assert hot(heater)
0> :step
1> :world
World 1:
  hot(heater)
  off(heater)
```

The rule `hot(X) => off(X)` fired. Now suppose the heater cools down — we
assert nothing about it being hot and step again:

```
1> :step
2> :world
World 2:
  on(heater)
```

Under the Closed World Assumption, `hot(heater)` is no longer true at world 2,
so `~hot(X) => on(X)` fires and the heater turns on.

## 3. Querying

```
2> :query on(X)
Yes.
  X = heater
2> :query off(X)
No.
```

## 4. Viewing history

```
2> :history
World 0:
World 1:
  hot(heater)
  off(heater)
World 2:
  on(heater)
```

World 0 is empty because we had not yet asserted `hot(heater)` when the first
step ran (assertions apply to the *next* step).

---

## 5. Traffic light state machine

```
0> :reset
State reset.
0> :load examples/traffic_light.tpl
Loaded 6 rules and 0 pattern functions from examples/traffic_light.tpl
```

Start the light in `green` and let the timer run without expiring:

```
0> :assert green
0> :step
1> :world
World 1:
  green
```

The persistence rule `green /\ ~timer_expired => next green` keeps the light
green. Step again without asserting `timer_expired`:

```
1> :step
2> :world
World 2:
  green
```

Now trigger the timer:

```
2> :assert timer_expired
2> :step
3> :world
World 3:
  green
  timer_expired
  yellow
```

At world 3, both the asserted `timer_expired` and the previous `green` are
present, so the transition rule fires and `yellow` appears. On the next step,
the timer is no longer asserted:

```
3> :step
4> :world
World 4:
  yellow
```

Trigger the timer again to move to red:

```
4> :assert timer_expired
4> :step
5> :world
World 5:
  yellow
  timer_expired
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
  green
```

---

## 6. Append — pattern functions

```
0> :reset
State reset.
0> :load examples/append.tpl
Loaded 3 rules and 2 pattern functions from examples/append.tpl
0> :program
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
0> :step
1> :query combined(X)
Yes.
  X = [1, 2, 3, 4, 5]
  X = [4, 5, 1, 2, 3]
```

Both orderings are derived because the two `list` facts can unify with either
`X` or `Y`.

```
1> :query list(X)
Yes.
  X = [1, 2, 3]
  X = [4, 5]
```

---

## 7. Adding rules interactively

You can type rules directly at the prompt without loading a file:

```
0> :reset
State reset.
0> temperature(X) > 100 => alarm(X).
Added: temperature(X) > 100 => alarm(X).
0> :assert temperature(reactor, 150)
0> :step
1> :query alarm(X)
No.
```

Hmm — the rule expects `temperature(X)` (arity 1) but we asserted arity 2.
Let us fix it:

```
1> :reset
State reset.
0> temperature(X) > 100 => alarm.
Added: temperature(X) > 100 => alarm.
0> :assert temperature(150)
0> :step
1> :query alarm
Yes.
  {}
```

The empty substitution `{}` means the query matched with no variable bindings,
which is expected for the ground atom `alarm`.

---

## Tips

- **Assertions are consumed**: `:assert` queues a fact for the *next* `:step`.
  After that step the fact is present only if a rule continues to derive it.
- **Closed World Assumption**: anything not derived or asserted is false.
- **Previous-time operator (`@`)**: references the world from the prior step.
  At world 0 there is no prior world, so `@p` is always false.
- **`next` in rule heads**: the derived atom appears in the *next* world, not
  the current one.
