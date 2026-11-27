---- MODULE error_before_invariant_continue ----
\* options: -continue
\* With -continue too, TLC stops at the error ENABLED A meets on x = 0:
\* the invariant x = 3 violates is not reached.
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
