\* options: -length 5 -deadlock
---- MODULE enabled_primed ----
\* (ENABLED A)' in -symbolic: Lamport's TimerNext pattern with partial next
\* state, nested ENABLED, operator parameters across prime, and action invariant.
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

Inv ==
    /\ (state \in {"idle", "done", "cancelled"} => t = 0)
    /\ (state = "pending" => t <= now)
    /\ (t >= 0)
    /\ (ENABLED (Request /\ (ENABLED <<Respond>>_vars)')) <=> (state = "idle")
    /\ ~(ENABLED (Request /\ (ENABLED <<Respond>>_vars)' /\ FALSE))

ActionInv ==
    (ENABLED <<Respond>>_vars)' <=> (state' = "pending")
====
INIT Init
NEXT Next
INVARIANT Inv
INVARIANT ActionInv
