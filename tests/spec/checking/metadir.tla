---- MODULE metadir ----
\* options: -metadir meta
\* The states found kept in files of the directory meta: the same search,
\* to a violated invariant and its trace.
EXTENDS Naturals
VARIABLE x, y
Init == x = 0 /\ y \in {0, 1}
Next == \/ x < 4 /\ x' = x + 1 /\ UNCHANGED y
        \/ y' = 1 - y /\ UNCHANGED x
Inv == x + y < 5
====
INIT Init
NEXT Next
INVARIANT Inv
