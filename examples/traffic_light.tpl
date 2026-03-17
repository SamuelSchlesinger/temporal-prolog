% Traffic light controller — state machine with @-based persistence
% Uses @ (previous world) for persistence and transitions.

% Transitions: when the timer expires, schedule the next colour.
@green /\ timer_expired => next yellow.
@yellow /\ timer_expired => next red.
@red /\ timer_expired => next green.

% Persistence: stay in state if timer hasn't expired.
@green /\ ~timer_expired => green.
@yellow /\ ~timer_expired => yellow.
@red /\ ~timer_expired => red.
