% Pattern function showcase: recursive list append
% Demonstrates pattern function definitions (f(args) -> body.)
% resolved via backward chaining at query time.

% Pattern function definitions for list append
append([], X) -> X.
append([A|X], Y) -> [A|append(X, Y)].

% Some sample lists as facts
list([1, 2, 3]).
list([4, 5]).

% When two lists exist and append relates them, derive combined/1
list(X) /\ list(Y) /\ append(X, Y, Z) => combined(Z).
