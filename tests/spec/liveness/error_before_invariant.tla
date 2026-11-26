---- MODULE error_before_invariant ----
\* TLC evaluates ENABLED A as it expands x = 0, after its successor: the
\* error there comes before the invariant x = 3 violates.
EXTENDS Integers
VARIABLE x
Init == x = 0
A == x' = CHOOSE v \in {1} : v > x + 5
Next == x' = x + 1
Spec == Init /\ [][Next]_x
Inv == x < 3
P == []<>(ENABLED A)
====
SPECIFICATION Spec
INVARIANT Inv
PROPERTY P
