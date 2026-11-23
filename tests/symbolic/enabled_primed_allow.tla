\* options: -length 3
---- MODULE enabled_primed_allow ----
\* Issue #10 in -symbolic: (ENABLED A)' evaluates ENABLED A in the next state,
\* allowing x = 0 -> x' = 1 -> x' = 1 without deadlock.
VARIABLE
    \* @type: Int;
    x
A == x = 1 /\ x' = 2
Init == x = 0
Next == x' = 1 /\ (ENABLED A)'
====
INIT Init
NEXT Next
