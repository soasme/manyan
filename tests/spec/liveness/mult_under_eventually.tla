---- MODULE mult_under_eventually ----
\* Naturals defines a * b == TRUE, so to_tf() must check level_in_bound()
\* when level_in() is 0, matching TLC's Liveness.astToLive().
\* options: -deadlock
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Spec == Init /\ [][Next]_x
P1 == <>(1 * x = 0)
P2 == <>(x * 1 = 0)
P3 == <>(x * x = 0)
P4 == []<>(1 * x' = 2)
====
SPECIFICATION Spec
PROPERTY P1
PROPERTY P2
PROPERTY P3
PROPERTY P4
