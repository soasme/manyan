---- MODULE dump_error_closed ----
\* An error in TLC's temporal checks as it expands a state: -dump dot
\* writes its steps once more and closes the graph.
\* options: -dump dot states
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
