---- MODULE Stepper ----
EXTENDS Naturals
CONSTANT Step(_, _)
VARIABLE v
Next == Step(v, v') /\ v < 6
====
