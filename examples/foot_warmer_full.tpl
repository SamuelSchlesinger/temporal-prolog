% Foot warmer controller — Sakuragawa 1986
% Simplified to use temp_high/temp_low predicates

temp_high(X) => off(X).
temp_low(X) => on(X).
