---- MODULE tautology_eventually ----
\* TLC does not fold <>FALSE to FALSE in LNEven.simplify(), so these
\* properties are checked rather than rejected as tautologies.
\* options: -deadlock
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Spec == Init /\ [][Next]_x
P1 == FALSE ~> FALSE
P2 == FALSE ~> TRUE
P3 == [](FALSE ~> FALSE)
P4 == (1 \in {2}) ~> (x = 7)
P5 == <>FALSE => []FALSE
====
SPECIFICATION Spec
PROPERTY P1
PROPERTY P2
PROPERTY P3
PROPERTY P4
PROPERTY P5
