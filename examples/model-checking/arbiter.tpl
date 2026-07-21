% A nondeterministic two-client resource arbiter.
%
% With simultaneous requests the negative SCC has exactly two minimal worlds:
% grant(1) or grant(2).  The chosen grant becomes ownership on the next tick.
request(X) /\ request(Y) /\ X != Y /\ ~grant(Y) => grant(X).
grant(X) => next owns(X).

% Ownership persists until that client is released.
@owns(X) /\ ~release(X) => owns(X).

% The scenario forbids this derived witness.
owns(X) /\ owns(Y) /\ X != Y => violation(mutual_exclusion).
