% Examples drawn from Sakuragawa 1986 — Temporal Prolog

% === Mutual exclusion (paper section 4.6) ===
% A resource can be assigned to at most one process at a time.
% @assigned_to(X) means "assigned_to(X) held at the previous step".

% If process X requests and was previously assigned, stay assigned.
assign(X) /\ @assigned_to(X) => assigned_to(X).

% If process 1 requests and nobody was previously assigned, assign to 1.
assign(1) /\ ~@assigned_to_something => assigned_to(1).

% Process 2 only gets the resource if process 1 is not also requesting
% and nobody was previously assigned (priority scheme).
assign(2) /\ ~assign(1) /\ ~@assigned_to_something => assigned_to(2).

% Track that something is assigned (for the negation checks above).
assigned_to(X) => assigned_to_something.
