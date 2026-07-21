append([], X) -> X.
append([H|T], Y) -> [H|append(T, Y)].
left([1, 2]).
right([3, 4]).
left(X) /\ right(Y) /\ append(X, Y) = Z => joined(Z).
