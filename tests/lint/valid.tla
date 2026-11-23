---- MODULE valid ----
EXTENDS Naturals, Sequences
CONSTANT N
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % N
Spec == Init /\ [][Next]_x /\ WF_x(Next)
====
