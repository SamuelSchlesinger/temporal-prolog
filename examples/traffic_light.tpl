% Traffic light controller — state machine with temporal logic
% Uses "next" to schedule the successor state and negation for persistence.

% Transitions: when the timer expires, move to the next colour.
green /\ timer_expired => next yellow.
yellow /\ timer_expired => next red.
red /\ timer_expired => next green.

% Persistence: stay in the current state while the timer has not expired.
green /\ ~timer_expired => next green.
yellow /\ ~timer_expired => next yellow.
red /\ ~timer_expired => next red.
