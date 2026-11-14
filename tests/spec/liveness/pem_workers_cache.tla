---- MODULE pem_workers_cache ----
\* The error models of one product are searched by the workers, but one
\* whose fairness uses TLCCache, which only the search may, is searched
\* again by it, in order.
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Up == x < 2 /\ x' = x + 1
Down == x = 2 /\ x' = 0
Next == Up \/ Down
Spec == Init /\ [][Next]_x /\ WF_x(Up /\ TLCCache(TRUE, x)) /\ WF_x(Down)
P == []<>(x = 2) /\ []<>(x = 3)
====
SPECIFICATION Spec
PROPERTY P
CHECK_DEADLOCK FALSE
