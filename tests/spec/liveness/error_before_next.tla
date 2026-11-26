---- MODULE error_before_next ----
\* The error in ENABLED A on x = 0 comes before the one in Next on x = 1.
EXTENDS Integers
VARIABLE x
Init == x = 0
A == x' = CHOOSE v \in {1} : v > x + 5
Next == (x < 1 /\ x' = x + 1) \/ (x = 1 /\ A)
Spec == Init /\ [][Next]_x
P == []<>(ENABLED A)
====
SPECIFICATION Spec
PROPERTY P
