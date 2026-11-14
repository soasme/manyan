---- MODULE reprint_counterexample ----
\* TLC rebuilds a temporal property's counterexample from Init, each state
\* from the one before, so Init and Next print again.
EXTENDS Naturals, TLC
VARIABLE l
Init == l = 1 /\ PrintT(<<"init">>)
Next == l < 4 /\ l' = l + 1 /\ PrintT(<<"step", l>>)
Spec == Init /\ [][Next]_l
P == <>(l = 5)
====
SPECIFICATION Spec
PROPERTY P
CHECK_DEADLOCK FALSE
