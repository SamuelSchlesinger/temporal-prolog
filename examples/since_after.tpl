% Since and after operators (past-time binary temporal operators)
%
% "c since d" is true when d held at some past time and c has held
% continuously from that moment up to and including now.
%
% In the paper's step 2(4), "c after d" records which event is newer:
% c establishes the condition, it persists, and the next d clears it.
% If c and d occur together, c establishes the condition in that world.

% The alarm stays active as long as it has been on since the trigger.
alarm_active since trigger => alarm_on.

% Monitoring is more recent than the last restart, and remains so until the
% next restart.
monitoring after restart => check_system.

% If the system was checked and is now stable, clear it.
check_system /\ stable => cleared.
