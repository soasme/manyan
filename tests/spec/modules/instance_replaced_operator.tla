---- MODULE instance_replaced_operator ----
\* A constant operator an instance substitutes, which the configuration
\* replaces with a definition: a call of it, its argument v' assigned, as
\* TLC (tlaplus/Examples' MCNano).
EXTENDS Naturals
CONSTANT Step(_, _)
VARIABLE v
Impl(a, b) == b = a + 1
I == INSTANCE Counter
Spec == I!Init /\ [][I!Next]_v
====
CONSTANT Step <- Impl
SPECIFICATION Spec
