% Arithmetic, comparison, and unification built-ins.
value(X) /\ Y is X + 1 => successor(Y).
value(X) /\ X * 2 >= 10 => large(X).
Y is div(10, 3) => quotient(Y).
pair(X, X) => repeated(X).
