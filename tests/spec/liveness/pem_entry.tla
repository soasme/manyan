---- MODULE pem_entry ----
\* A component reached by an edge that breaks the <>[] condition is
\* searched from the target of that edge.
VARIABLE s
Init == s = 1
Next == s' = 3
Spec == Init /\ [][Next]_s /\ WF_s(Next)
P == []<><<s' \in {1, 3}>>_s
====
SPECIFICATION Spec
PROPERTY P
CHECK_DEADLOCK FALSE
