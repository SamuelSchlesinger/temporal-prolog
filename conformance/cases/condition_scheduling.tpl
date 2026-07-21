% Positive conjunction is evaluated in a binding-safe order, not textually.
value(4).
Y is X + 1 /\ value(X) => arithmetic_result(Y).

X > 0 => positive(X) -> yes.
positive(X, Y) /\ value(X) => pattern_result(Y).

Y is X + 1 /\ value(X) => computed(Key) -> Y.
computed_result(computed(key)).
