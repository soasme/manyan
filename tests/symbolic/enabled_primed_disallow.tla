\* options: -length 3
---- MODULE enabled_primed_disallow ----
\* Issue #10 in -symbolic: (ENABLED A)' evaluates ENABLED A in the next state,
\* disallowing x = 0 -> x' = 1 and reaching deadlock at the initial state.
VARIABLE
    \* @type: Int;
    x
A == x = 0 /\ x' = 0
Init == x = 0
Next == x' = 1 /\ (ENABLED A)'
====
INIT Init
NEXT Next
