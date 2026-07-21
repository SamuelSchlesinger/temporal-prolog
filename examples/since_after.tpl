% Since and after operators (past-time binary temporal operators)
%
% "c since d" is true when d held at some past time and c has held
% continuously from that moment up to and including now.
%
% The paper's prose definition of "c after d" requires d at a strictly
% earlier world and c at a later world. Once witnessed it remains true. The
% printed step 2(4) implements a different "newer event" relation and is an
% erratum corrected by this project.

% The alarm stays active as long as it has been on since the trigger.
alarm_active since trigger => alarm_on.

% Monitoring occurred strictly after some restart.
monitoring after restart => check_system.

% If the system was checked and is now stable, clear it.
check_system /\ stable => cleared.
