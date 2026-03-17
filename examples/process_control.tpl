% Process lifecycle with temporal operators

% Starting a process makes it run forever (until explicitly stopped)
start(X) => running(X) until stop(X).

% A running process that encounters an error should raise alarm
running(X) /\ error(X) => alarm(X).

% Track history: if there was an error in the past
@had_error(X) => had_error(X).
error(X) => had_error(X).

% If a process had errors in the past and is restarted, flag it
start(X) /\ had_error(X) => needs_review(X).
