---- MODULE pem_workers_groups ----
\* The workers check the groups of error models, one tableau each, before
\* the search, which checks again in order those not found to hold: one
\* that uses TLCCache, which only the search may, and the last, violated.
EXTENDS Naturals, TLCExt
VARIABLE x
Next == x' = (x + 1) % 4
Spec == x = 0 /\ [][Next]_x /\ WF_x(Next)
P == \A p \in 0..3 : (x = p) ~> (x = (p + 1) % 4 /\ TLCCache(TRUE, p))
Q == []<>(x = 7)
====
SPECIFICATION Spec
PROPERTY P
PROPERTY Q
