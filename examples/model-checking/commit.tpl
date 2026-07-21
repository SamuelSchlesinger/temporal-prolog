% A small atomic-commit coordinator for two named participants.
participant(p1).
participant(p2).

begin(T) => next voting(T).

% Commit requires every yes vote; any explicit no vote aborts.
voting(T) /\ vote_yes(T, p1) /\ vote_yes(T, p2) => next committed(T).
voting(T) /\ participant(P) /\ vote_no(T, P) => next aborted(T).

% Decisions, once reached, are durable.
committed(T) => always decision(T, commit).
aborted(T) => always decision(T, abort).

% A safety witness consumed by the scenario invariant.
decision(T, commit) /\ decision(T, abort) => violation(atomic_decision, T).
