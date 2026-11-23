---- MODULE enabled_primed ----
\* (ENABLED A)' evaluates ENABLED A in the next state (two steps ahead), as in
\* Lamport's RealTime TimerNext: cancelling a pending request disables Respond
\* in the next state and resets t to 0, while ticks keep Respond enabled.
EXTENDS Naturals
VARIABLES state, now, t
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

Inv ==
    /\ (state \in {"idle", "done", "cancelled"} => t = 0)
    /\ (state = "pending" => t <= now)
    /\ (t >= 0)
====
INIT Init
NEXT Next
INVARIANT Inv
CHECK_DEADLOCK FALSE
