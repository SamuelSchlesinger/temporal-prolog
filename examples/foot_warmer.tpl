% Foot warmer controller from Sakuragawa 1986, Section 4.2
% temperature_of_foot_warmer(X) > comfortable_temperature => off_foot_warmer(X).
% temperature_of_foot_warmer(X) < comfortable_temperature => on_foot_warmer(X).

% Simplified version for testing:
% We use device(X) as a domain fact to bind X before negation.
device(heater).
device(X) /\ hot(X) => off(X).
device(X) /\ ~hot(X) => on(X).
