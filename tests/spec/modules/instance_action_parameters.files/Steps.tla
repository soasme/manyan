---- MODULE Steps ----
EXTENDS Naturals
CONSTANT K
VARIABLE v
A(x) == v' = v + K + x /\ v < 9
B == \E x \in {1, 2} : v' = v + x + K /\ v < 9
====
