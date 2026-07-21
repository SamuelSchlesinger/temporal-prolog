% Formula keywords remain available as constructor names in term position.
keyword_terms(always, since, after, for, until, atnext, eventually, next,
              true, false, is).

% External predicates also accept the call form admitted by the grammar.
true() /\ is(X, 2 + 3) => prefix_builtin(X).
false() => impossible.
