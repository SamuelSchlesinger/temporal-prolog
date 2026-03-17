% Test temporal operators
% Simple: if hot, turn off. If not hot, turn on.
% We use device(X) as a domain fact to bind X before negation.
device(heater).
device(X) /\ hot(X) => off(X).
device(X) /\ ~hot(X) => on(X).

% With memory: if was previously on and still hot, signal warning
@on(X) /\ hot(X) => warning(X).
