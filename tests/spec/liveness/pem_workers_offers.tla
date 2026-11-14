---- MODULE pem_workers_offers ----
\* The workers evaluate the conditions of the offers of a product's
\* components before them, but leave one that uses TLCCache, which only
\* the search may, to the search.
EXTENDS Naturals, TLCExt
VARIABLE x
Next == x' = (x + 1) % 12000
Spec == x = 0 /\ [][Next]_x /\ WF_x(Next)
P == /\ []<><<x' = 1 /\ TLCCache(TRUE, x)>>_x
     /\ []<><<x' = 2>>_x /\ []<><<x' = 3>>_x /\ []<><<x' = 4>>_x
     /\ []<><<x' = 5>>_x /\ []<><<x' = 6>>_x /\ []<><<x' = 7>>_x
     /\ []<><<x' = 8>>_x /\ []<><<x' = 9>>_x
====
SPECIFICATION Spec
PROPERTY P
