---- MODULE error_property_unbounded ----
\* ENABLED A fails on every state of a state space without end: TLC
\* stops at the first, as it evaluates P on each state it expands.
EXTENDS Integers
VARIABLE x
Init == x = 0
A == x' = CHOOSE v \in {1} : v > x + 5
Next == x' = x + 1
Spec == Init /\ [][Next]_x
P == []<>(ENABLED A)
====
SPECIFICATION Spec
PROPERTY P
