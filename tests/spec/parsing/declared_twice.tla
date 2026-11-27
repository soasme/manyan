---- MODULE declared_twice ----
\* A constant or variable declared again as it was: SANY warns and keeps
\* the first, and TLC checks the model.
EXTENDS Naturals
CONSTANT N, N
VARIABLE x, x
Init == x = 0
Next == x < N /\ x' = x + 1
Inv == x < 2
====
CONSTANT N = 3
INIT Init
NEXT Next
INVARIANT Inv
