% Since and after operators (past-time binary temporal operators)
%
% "c since d" is true when d held at some past time and c has held
% continuously from that moment up to and including now.
%
% "c after d" is true when d held at some past time and c held at some
% time strictly after d (not necessarily continuously).

% The alarm stays active as long as it has been on since the trigger.
alarm_active since trigger => alarm_on.

% After a restart, the system needs to be checked.
monitoring after restart => check_system.

% If the system was checked and is now stable, clear it.
check_system /\ stable => cleared.
