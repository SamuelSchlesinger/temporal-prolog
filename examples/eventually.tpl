% Past-time temporal operators: eventually (once)
% "eventually c" is a synonym for "once c" — true if c held at some
% past time step (including the current one).

% If the alarm was ever triggered and we are currently in maintenance mode,
% generate a review request.
eventually alarm /\ maintenance => review_needed.

% If a sensor ever reported a critical value, flag it permanently.
eventually critical_reading => flagged.

% Once flagged and now cleared, mark as resolved.
flagged /\ cleared => resolved.
