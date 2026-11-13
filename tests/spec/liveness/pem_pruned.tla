---- MODULE pem_pruned ----
\* As TLC, a property without a tableau is searched by the edges that
\* keep its <>[] condition: state 3, reached only by others, is a root
\* after the initial states, so the component found first is of state 2.
VARIABLE s
Succ == <<{3}, {1, 2, 3}, {3}>>
Init == s \in {1, 2, 3}
Next == s' \in Succ[s]
A0 == s' \in <<{3}, {2}, {}>>[s]
Spec == Init /\ [][Next]_s /\ WF_s(A0)
P == []<><<s' \in {1, 3}>>_s
====
SPECIFICATION Spec
PROPERTY P
CHECK_DEADLOCK FALSE
