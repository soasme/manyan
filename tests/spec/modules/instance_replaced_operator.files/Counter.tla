---- MODULE Counter ----
EXTENDS Naturals
CONSTANT Step(_, _)
VARIABLE v
Init == v = 1
Next == Step(v, v') /\ v < 3
====
