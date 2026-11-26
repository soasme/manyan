---- MODULE tableau_true_root ----
\* The negation <>TRUE: an initial node holds TRUE and steps to the empty
\* node, at the initial state's own stuttering, where TLC stops.
VARIABLE s
Succ == <<{3}, {}, {1, 3}>>
Init == s = 3
Next == s' \in Succ[s]
Spec == Init /\ [][Next]_s
P == ~<>TRUE
====
SPECIFICATION Spec
PROPERTY P
CHECK_DEADLOCK FALSE
