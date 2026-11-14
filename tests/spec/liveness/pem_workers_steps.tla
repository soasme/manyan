---- MODULE pem_workers_steps ----
\* The workers evaluate the <>[] actions of the error models on the
\* product's edges before searching them, but leave one that uses
\* TLCCache, which only the search may, to the search.
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Up == x < 2 /\ x' = x + 1
Down == x = 2 /\ x' = 0
Next == Up \/ Down
Spec == Init /\ [][Next]_x /\ WF_x(Up) /\ WF_x(Down)
P == []<><<Down /\ TLCCache(TRUE, x) /\ x' = 5>>_x /\ []<>(x = 3)
====
SPECIFICATION Spec
PROPERTY P
CHECK_DEADLOCK FALSE
