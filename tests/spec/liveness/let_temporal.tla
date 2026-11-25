---- MODULE let_temporal ----
\* A LET with a temporal body under [], <>, ~> or ~ must be expanded, as TLC does.
\* options: -deadlock
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
Spec == Init /\ [][Next]_x
P1 == [](LET c == 1 IN <>(x = 3))
P2 == [](LET y == x IN <>(y = 3))
P3 == <>(LET c == 1 IN [](x = 3))
P4 == (LET c == 1 IN <>(x = 3)) ~> (x = 3)
P5 == (LET LocalOp(p) == p IN []FALSE) ~> FALSE
====
SPECIFICATION Spec
PROPERTY P1
PROPERTY P2
PROPERTY P3
PROPERTY P4
PROPERTY P5
