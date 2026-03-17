% Foot warmer controller from Sakuragawa 1986, Section 4.2
% temperature_of_foot_warmer(X) > comfortable_temperature => off_foot_warmer(X).
% temperature_of_foot_warmer(X) < comfortable_temperature => on_foot_warmer(X).

% Simplified version for testing:
hot(X) => off(X).
~hot(X) => on(X).
