---- MODULE dump_initial_violation ----
\* An initial state that violates an invariant stops TLC with the states
\* it wrote unflushed: -dump leaves the file empty.
\* options: -dump states
EXTENDS Naturals
VARIABLE x
Init == x \in {0, 1, 2}
Next == x < 3 /\ x' = x + 1
Inv == x # 1
====
INIT Init
NEXT Next
INVARIANT Inv
