---- MODULE error_enabled_fingerprint ----
\* A successor ENABLED cannot fingerprint: TLC reports only the behavior.
EXTENDS Integers
VARIABLE x
Init == x = 0
B == x' = <<>>[1]
Next == x' = 1 - x
Spec == Init /\ [][Next]_x
P == []<>(ENABLED B)
====
SPECIFICATION Spec
PROPERTY P
