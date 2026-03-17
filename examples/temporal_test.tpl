% Test temporal operators
% Simple: if hot, turn off. If not hot, turn on.
hot(X) => off(X).
~hot(X) => on(X).

% With memory: if was previously on and still hot, signal warning
@on(X) /\ hot(X) => warning(X).
