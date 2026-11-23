\* options: -length 5 -deadlock
---- MODULE enabled_primed_reach ----
\* Reachability counterpart to enabled_primed: while Cancel resets t to 0 via
\* ~(ENABLED <<Respond>>_vars)', Tick keeps Respond enabled in the next state
\* so t reaches 2 (Request then two Ticks), violating t < 2 at depth 3.
EXTENDS Naturals
VARIABLES
    \* @type: Str;
    state,
    \* @type: Int;
    now,
    \* @type: Int;
    t
\* @type: <<Str, Int>>;
vars == <<state, now>>

Init == state = "idle" /\ now = 0 /\ t = 0

Request == state = "idle" /\ state' = "pending" /\ UNCHANGED now
Respond == state = "pending" /\ state' = "done" /\ UNCHANGED now
Cancel  == state = "pending" /\ state' = "cancelled" /\ UNCHANGED now
Tick    == now < 3 /\ now' = now + 1 /\ UNCHANGED state

Step == Request \/ Respond \/ Cancel \/ Tick

TimerNext ==
    t' = IF <<Respond>>_vars \/ ~(ENABLED <<Respond>>_vars)'
         THEN 0
         ELSE t + (now' - now)

Next == Step /\ TimerNext
NotReach2 == t < 2
====
INIT Init
NEXT Next
INVARIANT NotReach2
