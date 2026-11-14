---- MODULE reprint_tableau ----
\* TLC's tableau checker generates a state's successors again where its
\* product meets the state anew, so Next prints again: the initial state's.
EXTENDS Naturals, TLC
VARIABLE l
Init == l = 1
Next == l < 4 /\ l' = l + 1 /\ PrintT(<<"step", l>>)
Spec == Init /\ [][Next]_l
P == [](l <= 3 => [](l > 0))
====
SPECIFICATION Spec
PROPERTY P
CHECK_DEADLOCK FALSE
