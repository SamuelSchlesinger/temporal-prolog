% Future-time next operator
% "next r" means the result holds at the next time step, not the current one.
% This lets you schedule effects one step into the future.

% When a request arrives, acknowledge it immediately.
request(X) => ack(X).

% Also schedule processing for the next step.
request(X) => next process(X).

% After processing, schedule completion for the following step.
process(X) => next done(X).

% A done task can be reported.
done(X) => report(X).
