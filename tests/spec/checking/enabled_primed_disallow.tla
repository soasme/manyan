---- MODULE enabled_primed_disallow ----
\* Issue #10: (ENABLED A)' evaluates ENABLED A in the next state, so x = 0
\* cannot transition to x' = 1 where A (x = 0 /\ x' = 0) is disabled.
VARIABLE x
A == x = 0 /\ x' = 0
Init == x = 0
Next == x' = 1 /\ (ENABLED A)'
====
INIT Init
NEXT Next
