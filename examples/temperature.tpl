% Temperature monitor from Sakuragawa 1986, Section 4.4
% Simplified: if temp is dangerous, raise alarm

temp_is(X, C) /\ C > 100 => dangerous(X).
dangerous(X) => alarm.
