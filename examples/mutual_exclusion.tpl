% Mutual exclusion from Sakuragawa 1986, Section 4.6
% Simplified for ground instances

% If process X requests and was previously assigned, stay assigned
assign(X) /\ @assigned_to(X) => assigned_to(X).

% If process 1 requests and nobody else was assigned, assign to 1
assign(1) /\ ~@assigned_to_something => assigned_to(1).

% If process 2 requests, process 1 doesn't, and nobody assigned
assign(2) /\ ~assign(1) /\ ~@assigned_to_something => assigned_to(2).

% Track that something is assigned
assigned_to(X) => assigned_to_something.
