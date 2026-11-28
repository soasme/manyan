---- MODULE dump_states_violation ----
\* options: -dump found.dump
\* The states found up to a violated invariant, of one variable.
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == x < 2
====
INIT Init
NEXT Next
INVARIANT Inv
