% Conditional pattern-function reduction from paper Section 5.1.
enabled(X) => choose(X) -> selected.
request(X) /\ choose(X) = Y => result(Y).
