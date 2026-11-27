---- MODULE inst_unused_param ----
\* As SANY, an instance's parameter is bounded only where the definition
\* used uses it: J(x')!No is legal, as No does not use u.
EXTENDS Naturals, TLC
VARIABLE x
J(w) == INSTANCE InstC WITH u <- w
Init == x = 0
Next == x < 2 /\ x' = x + 1 /\ PrintT(J(x')!No)
====
INIT Init
NEXT Next
CHECK_DEADLOCK FALSE
