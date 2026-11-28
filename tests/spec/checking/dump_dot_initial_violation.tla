---- MODULE dump_dot_initial_violation ----
\* So -dump dot leaves the graph as it began, unclosed.
\* options: -dump dot states
EXTENDS Naturals
VARIABLE x
Init == x \in {0, 1, 2}
Next == x < 3 /\ x' = x + 1
Inv == x # 1
====
INIT Init
NEXT Next
INVARIANT Inv
