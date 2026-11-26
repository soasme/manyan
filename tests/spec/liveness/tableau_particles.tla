---- MODULE tableau_particles ----
\* The negation <>TRUE /\ [](s # 9): the initial nodes hold the formula,
\* the nodes after them do not, so the lasso is TLC's.
\* options: -fp 99
VARIABLE s
Succ == <<{3}, {}, {1, 3}>>
Init == s = 3
Next == s' \in Succ[s]
Spec == Init /\ [][Next]_s
P == []FALSE \/ <>(s = 9)
====
SPECIFICATION Spec
PROPERTY P
CHECK_DEADLOCK FALSE
