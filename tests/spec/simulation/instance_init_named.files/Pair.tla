---- MODULE Pair ----
EXTENDS Naturals
VARIABLE v, w
Init == v = 1 /\ w = 2
Next == v' = v + 1 /\ w' = w
====
