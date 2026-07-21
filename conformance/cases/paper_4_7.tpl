% Range-restricted form of the published Section 4.7 program.
assign(X) /\ ~assigned_to_another(X) => assigned_to(X).
assigned_to(X) /\ assign(Y) /\ X != Y => assigned_to_another(Y).
