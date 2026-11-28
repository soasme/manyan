---- MODULE dump_stuttering ----
\* -dump with temporal properties: TLC writes each state again after its
\* successors, its stuttering step, and numbers the states as written.
\* options: -deadlock -dump states
EXTENDS Naturals
VARIABLE x
Init == x \in {0, 5}
Next == x < 2 /\ x' = x + 1
Spec == Init /\ [][Next]_x
P == <>(x >= 0)
====
SPECIFICATION Spec
PROPERTY P
