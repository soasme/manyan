---- MODULE enabled_primed_allow ----
\* Issue #10: (ENABLED A)' evaluates ENABLED A in the next state, so x = 0
\* transitions to x' = 1 where A (x = 1 /\ x' = 2) is enabled.
VARIABLE x
A == x = 1 /\ x' = 2
Init == x = 0
Next == x' = 1 /\ (ENABLED A)'
====
INIT Init
NEXT Next
