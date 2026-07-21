% Both models are classical-minimal within one negative SCC. In the second,
% p(a) is unsupported but blocks q(a), as permitted by the paper's semantics.
domain(X) /\ ~p(X) => q(X).
q(X) /\ impossible => p(X).
domain(a).
