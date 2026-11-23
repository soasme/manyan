\* options: -length 6 -deadlock
---- MODULE enabled_primed_fair ----
\* WF of an action guarded by (ENABLED B)' in -symbolic: at x = 2, stepping to
\* x' = 3 disables B in the next state, so the fair action is disabled and the
\* behavior may stutter at x = 2, violating <>(x = 3).
EXTENDS Naturals
VARIABLE
    \* @type: Int;
    x
Init == x = 0
Next == x < 4 /\ x' = x + 1
B == x < 3 /\ x' = x + 1
Spec == Init /\ [][Next]_x /\ WF_x(Next /\ (ENABLED B)')
Eventually3 == <>(x = 3)
====
SPECIFICATION Spec
PROPERTY Eventually3
