---- MODULE enabled_nested ----
\* Nested ENABLED with priming (2-step and 3-step lookahead), UNCHANGED of
\* ENABLED, and LET / operator parameter bindings across prime into ENABLED.
EXTENDS Naturals
VARIABLES x, y

A == x < 2 /\ x' = x + 1
B == x < 3 /\ x' = x + 1

Op(p) == p = 0 /\ (ENABLED (y' = p /\ y' = 1))'
OpEnabled(p) == x = 1 => (p /\ ~p')

Init ==
    /\ x = 0 /\ y = 0
    /\ ENABLED (x' = x + 1 /\ (ENABLED A)')
    /\ ~(ENABLED (x' = x + 1 /\ (ENABLED A)' /\ FALSE))

Next ==
    /\ x < 4
    /\ x' = x + 1
    /\ y' = IF (ENABLED B)' THEN 1 ELSE 0
    /\ (x = 0 => LET p == x IN p = 0 /\ (ENABLED (y' = p /\ y' = 1))')
    /\ (x = 0 => Op(x))
    /\ OpEnabled(ENABLED A)
    /\ (x = 0 => (ENABLED (x' = x + 1 /\ (ENABLED B)'))')
    /\ (x = 0 => ~(ENABLED (x' = x + 1 /\ (ENABLED A)'))')
    /\ (UNCHANGED (ENABLED A) <=> (x /= 1))

Inv ==
    /\ (x \in {1, 2} => y = 1)
    /\ (x \in {0, 3, 4} => y = 0)
    /\ (ENABLED (x' = x + 1 /\ (ENABLED A)')) <=> (x = 0)
    /\ (ENABLED (x' = x + 1 /\ (ENABLED B)')) <=> (x \in {0, 1})
    /\ ~(ENABLED (x' = x + 1 /\ (ENABLED B)' /\ FALSE))
====
INIT Init
NEXT Next
INVARIANT Inv
CHECK_DEADLOCK FALSE
