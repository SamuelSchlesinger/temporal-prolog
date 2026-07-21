% Deliberately broken atomic commit: one yes commits while one no aborts.
participant(p1).
participant(p2).

begin(T) => next voting(T).
voting(T) /\ participant(P) /\ vote_yes(T, P) => next committed(T).
voting(T) /\ participant(P) /\ vote_no(T, P) => next aborted(T).

committed(T) => always decision(T, commit).
aborted(T) => always decision(T, abort).
decision(T, commit) /\ decision(T, abort) => violation(atomic_decision, T).
